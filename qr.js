/* qr.js -- QR code generator in Javascript (revision 2011-01-19)
 * Written by Kang Seonghoon <public+qrjs@mearie.org>.
 *
 * This source code is in the public domain; if your jurisdiction does not
 * recognize the public domain the terms of Creative Commons CC0 license
 * apply. In the other words, you can always do what you want.
 */

/* Quick overview: QR code composed of 2D array of modules (a rectangular
 * area that conveys one bit of information); some modules are fixed to help
 * the recognition of the code, and remaining data modules are further divided
 * into 8-bit code words which are augumented by Reed-Solomon error correcting
 * codes (ECC). There could be multiple ECCs, in the case the code is so large
 * that it is helpful to split the raw data into several chunks.
 *
 * The number of modules is determined by the code's "version", ranging from 1
 * (21x21) to 40 (177x177). How many ECC bits are used is determined by the
 * ECC level (L/M/Q/H). The number and size (and thus the order of generator
 * polynomial) of ECCs depend to the version and ECC level.
 */
// per-version information (cf. JIS X 0510:2004 pp. 30--36, 71)
//
// [0]: the degree of generator polynomial by ECC levels
// [1]: # of code blocks by ECC levels
// [2]: left-top positions of alignment patterns
//
// the number in this table (in particular, [0]) does not exactly match with
// the numbers in the specficiation. see augumenteccs below for the reason.
// mode constants (cf. Table 2 in JIS X 0510:2004 p. 16)
var MODE_TERMINATOR = 0;
var MODE_NUMERIC = 1, MODE_ALPHANUMERIC = 2, MODE_OCTET = 4, MODE_KANJI = 8;


// GF(2^8)-to-integer mapping with a reducing polynomial x^8+x^4+x^3+x^2+1
// invariant: GF256_MAP[GF256_INVMAP[i]] == i for all i in [1,256)
var GF256_MAP = [], GF256_INVMAP = [-1];
for (var i = 0, v = 1; i < 255; ++i) {
    GF256_MAP.push(v);
    GF256_INVMAP[v] = i;
    v = (v * 2) ^ (v >= 128 ? 0x11d : 0);
}

// generator polynomials up to degree 30
// (should match with polynomials in JIS X 0510:2004 Appendix A)
//
// generator polynomial of degree K is product of (x-\alpha^0), (x-\alpha^1),
// ..., (x-\alpha^(K-1)). by convention, we omit the K-th coefficient (always 1)
// from the result; also other coefficients are written in terms of the exponent
// to \alpha to avoid the redundant calculation. (see also calculateecc below.)
var GF256_GENPOLY = [[]];
for (var i = 0; i < 30; ++i) {
    var prevpoly = GF256_GENPOLY[i], poly = [];
    for (var j = 0; j <= i; ++j) {
        var a = (j < i ? GF256_MAP[prevpoly[j]] : 0);
        var b = GF256_MAP[(i + (prevpoly[j-1] || 0)) % 255];
        poly.push(GF256_INVMAP[a ^ b]);
    }
    GF256_GENPOLY.push(poly);
}

// alphanumeric character mapping (cf. Table 5 in JIS X 0510:2004 p. 19)
var ALPHANUMERIC_MAP = {};
for (var i = 0; i < 45; ++i) {
    ALPHANUMERIC_MAP['0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:'.charAt(i)] = i;
}


/*
 * |<--------------- n --------------->|
 * |        |<----- n-17 ---->|        |
 * +-------+                ///+-------+ ----
 * |       |                ///|       |    ^
 * |  9x9  |       @@@@@    ///|  9x8  |    |
 * |       | # # # @5x5@ # # # |       |    |
 * +-------+       @@@@@       +-------+    |
 *       #                               ---|
 *                                        ^ |
 *       #                                |
 *     @@@@@       @@@@@       @@@@@      | n
 *     @5x5@       @5x5@       @5x5@   n-17
 *     @@@@@       @@@@@       @@@@@      | |
 *       #                                | |
 * //////                                 v |
 * //////#                               ---|
 * +-------+       @@@@@       @@@@@        |
 * |       |       @5x5@       @5x5@        |
 * |  8x9  |       @@@@@       @@@@@        |
 * |       |                                v
 * +-------+                             ----
 *
 * when the entire code has n^2 modules and there are m^2-3 alignment
 * patterns, we have:
 * - 225 (= 9x9 + 9x8 + 8x9) modules for finder patterns and
 *   format information;
 * - 2n-34 (= 2(n-17)) modules for timing patterns;
 * - 36 (= 3x6 + 6x3) modules for version information, if any;
 * - 25m^2-75 (= (m^2-3)(5x5)) modules for alignment patterns
 *   if any, but 10m-20 (= 2(m-2)x5) of them overlaps with
 *   timing patterns.
 */
var ndatalenbits = function(ver, mode) {
    switch (mode) {
        case MODE_NUMERIC: return (ver < 10 ? 10 : ver < 27 ? 12 : 14);
        case MODE_ALPHANUMERIC: return (ver < 10 ? 9 : ver < 27 ? 11 : 13);
        case MODE_OCTET: return (ver < 10 ? 8 : 16);
        case MODE_KANJI: return (ver < 10 ? 8 : ver < 27 ? 10 : 12);
    }
}

// returns the code words (sans ECC bits) for given data and configurations.
// requires data to be preprocessed by validatedata. no length check is
// performed, and everything has to be checked before calling this function.
export default encode = function(ver, mode, data, maxbuflen) {
    var buf = [];
    var bits = 0, remaining = 8;
    var datalen = data.length;

    // this function is intentionally no-op when n=0.
    var pack = function(x, n) {
        if (n >= remaining) {
            buf.push(bits | (x >> (n -= remaining)));
            while (n >= 8) buf.push((x >> (n -= 8)) & 255);
            bits = 0;
            remaining = 8;
        }
        if (n > 0) bits |= (x & ((1 << n) - 1)) << (remaining -= n);
    };

    var nlenbits = ndatalenbits(ver, mode);
    pack(mode, 4);
    pack(datalen, nlenbits);

    switch (mode) {
        case MODE_NUMERIC:
            for (var i = 2; i < datalen; i += 3) {
                pack(parseInt(data.substring(i-2,i+1), 10), 10);
            }
            pack(parseInt(data.substring(i-2), 10), [0,4,7][datalen%3]);
            break;

        case MODE_ALPHANUMERIC:
            for (var i = 1; i < datalen; i += 2) {
                pack(ALPHANUMERIC_MAP[data.charAt(i-1)] * 45 +
                    ALPHANUMERIC_MAP[data.charAt(i)], 11);
            }
            if (datalen % 2 == 1) {
                pack(ALPHANUMERIC_MAP[data.charAt(i-1)], 6);
            }
            break;

        case MODE_OCTET:
            for (var i = 0; i < datalen; ++i) {
                pack(data[i], 8);
            }
            break;
    };

    // final bits. it is possible that adding terminator causes the buffer
    // to overflow, but then the buffer truncated to the maximum size will
    // be valid as the truncated terminator mode bits and padding is
    // identical in appearance (cf. JIS X 0510:2004 sec 8.4.8).
    pack(MODE_TERMINATOR, 4);
    if (remaining < 8) buf.push(bits);

    // the padding to fill up the remaining space. we should not add any
    // words when the overflow already occurred.
    while (buf.length + 1 < maxbuflen) buf.push(0xec, 0x11);
    if (buf.length < maxbuflen) buf.push(0xec);
    return buf;
}
