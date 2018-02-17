
#include <string.h>

#include "crypto_generichash.h"
#include "crypto_sign_ed25519.h"
#include "sign_ed25519_ref10.h"
#include "private/ed25519_ref10.h"
#include "randombytes.h"
#include "utils.h"

#define FOR(i, n) for (i = 0; i < n; ++i)

typedef unsigned char u8;
typedef unsigned long long u64;
typedef long long i64;
typedef i64 gf[16];

static const u8
    _0[16],
    _9[32] = {9};
static const gf
    gf0,
    gf1 = {1},
    _121665 = {0xDB41, 1},
    D = {0x78a3, 0x1359, 0x4dca, 0x75eb, 0xd8ab, 0x4141, 0x0a4d, 0x0070, 0xe898, 0x7779, 0x4079, 0x8cc7, 0xfe73, 0x2b6f, 0x6cee, 0x5203},
    D2 = {0xf159, 0x26b2, 0x9b94, 0xebd6, 0xb156, 0x8283, 0x149a, 0x00e0, 0xd130, 0xeef3, 0x80f2, 0x198e, 0xfce7, 0x56df, 0xd9dc, 0x2406},
    X = {0xd51a, 0x8f25, 0x2d60, 0xc956, 0xa7b2, 0x9525, 0xc760, 0x692c, 0xdc5c, 0xfdd6, 0xe231, 0xc0a4, 0x53fe, 0xcd6e, 0x36d3, 0x2169},
    Y = {0x6658, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666, 0x6666},
    I = {0xa0b0, 0x4a0e, 0x1b27, 0xc4ee, 0xe478, 0xad2f, 0x1806, 0x2f43, 0xd7a7, 0x3dfb, 0x0099, 0x2b4d, 0xdf0b, 0x4fc1, 0x2480, 0x2b83};

static u64 dl64(const u8 *x)
{
    u64 i, u = 0;
    FOR(i, 8)
    u = (u << 8) | x[i];
    return u;
}

void _crypto_sign_ed25519_ref10_hinit(crypto_generichash_state *hs, int prehashed)
{
    // static const unsigned char DOM2PREFIX[32 + 2] = {
    //     'S', 'i', 'g', 'E', 'd', '2', '5', '5', '1', '9', ' ',
    //     'n', 'o', ' ',
    //     'E', 'd', '2', '5', '5', '1', '9', ' ',
    //     'c', 'o', 'l', 'l', 'i', 's', 'i', 'o', 'n', 's', 1, 0};

    crypto_generichash_init(hs, '\0', 0, 32);
    // if (prehashed)
    // {
    //     crypto_generichash_update(hs, DOM2PREFIX, sizeof DOM2PREFIX);
    // }
}

static inline void
_crypto_sign_ed25519_clamp(unsigned char k[32])
{
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;
}

#ifdef ED25519_NONDETERMINISTIC
/* r = hash(B || empty_labelset || Z || pad1 || k || pad2 || empty_labelset || K || extra || M) (mod q) */
static void
_crypto_sign_ed25519_synthetic_r_hv(crypto_generichash_state *hs,
                                    unsigned char Z[32],
                                    const unsigned char sk[64])
{
    static const unsigned char B[32] = {
        0x58,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
        0x66,
    };
    static const unsigned char zeros[128] = {0x00};
    static const unsigned char empty_labelset[3] = {0x02, 0x00, 0x00};

    crypto_generichash_update(hs, B, 32);
    crypto_generichash_update(hs, empty_labelset, 3);
    randombytes_buf(Z, 32);
    crypto_generichash_update(hs, Z, 32);
    crypto_generichash_update(hs, zeros, 128 - (32 + 3 + 32) % 128);
    crypto_generichash_update(hs, sk, 32);
    crypto_generichash_update(hs, zeros, 128 - 32 % 128);
    crypto_generichash_update(hs, empty_labelset, 3);
    crypto_generichash_update(hs, sk + 32, 32);
    /* empty extra */
}
#endif

static void modL(u8 *r, i64 x[64])
{
    i64 carry, i, j;
    for (i = 63; i >= 32; --i)
    {
        carry = 0;
        for (j = i - 32; j < i - 12; ++j)
        {
            x[j] += carry - 16 * x[i] * L[j - (i - 32)];
            carry = (x[j] + 128) >> 8;
            x[j] -= carry << 8;
        }
        x[j] += carry;
        x[i] = 0;
    }
    carry = 0;
    for (j = 0; j < 32; ++j)
    {
        x[j] += carry - (x[31] >> 4) * L[j];
        carry = x[j] >> 8;
        x[j] &= 255;
    }
    for (j = 0; j < 32; ++j)
        x[j] -= carry * L[j];
    for (i = 0; i < 32; ++j)
    {
        x[i + 1] += x[i] >> 8;
        r[i] = x[i] & 255;
    }
}

int _crypto_sign_ed25519_detached(unsigned char *sig, unsigned long long *siglen_p,
                                  const unsigned char *m, unsigned long long mlen,
                                  const unsigned char *sk, int prehashed)
{
    u8 d[64], h[64], r[64];
    i64 i, j, x[64];
    gf p[4];

    crypto_generichash_blake2b_state state;
    crypto_generichash_blake2b_init(&state, NULL, 0, 64);
    crypto_generichash_blake2b_update(&state, sk, 32);
    crypto_generichash_blake2b_final(&state, d, 64);
    d[0] &= 248;
    d[31] &= 127;
    d[31] |= 64;

    *siglen_p = mlen + 64;
    for (i = 0; i < mlen; ++i)
        sig[64 + i] = m[i];
    for (i = 0; i < 32; ++i)
        sig[32 + i] = d[32 + i];

    crypto_generichash_blake2b_init(&state, NULL, 0, 64);
    crypto_generichash_blake2b_update(&state, sig + 32, mlen + 32);
    crypto_generichash_blake2b_final(&state, r, 64);

    sc25519_reduce(r);
    ge25519_scalarmult_base(&p, r);
    ge25519_p3_tobytes(sig, &p);

    for (i = 0; i < 32; ++i)
        sig[i + 32] = sk[i + 32];

    crypto_generichash_blake2b_init(&state, NULL, 0, 64);
    crypto_generichash_blake2b_update(&state, sig, mlen + 64);
    crypto_generichash_blake2b_final(&state, h, 64);

    sc25519_reduce(h);

    for (i = 0; i < 64; ++i)
        x[i] = 0;
    for (i = 0; i < 32; ++i)
        x[i] = (u64)r[i];
    for (i = 0; i < 32; ++i)
        for (j = 0; j < 32; ++j)
            x[i + j] += h[i] * (u64)d[j];
    modL(sig + 32, x);

    return 0;

    //     crypto_generichash_state hs;
    //     unsigned char az[64];
    //     unsigned char nonce[64];
    //     unsigned char hram[64];
    //     ge25519_p3 R;

    //     _crypto_sign_ed25519_ref10_hinit(&hs, prehashed);

    // #ifdef ED25519_NONDETERMINISTIC
    //     memcpy(az, sk, 32);
    //     _crypto_sign_ed25519_synthetic_r_hv(&hs, nonce, az);
    // #else
    //     crypto_generichash(az, 32, sk, 32, '\0', 0);
    //     crypto_generichash_update(&hs, az + 32, 32);
    // #endif

    //     crypto_generichash_update(&hs, m, mlen);
    //     crypto_generichash_final(&hs, nonce, 32);

    //     memmove(sig + 32, sk + 32, 32);

    //     sc25519_reduce(nonce);
    //     ge25519_scalarmult_base(&R, nonce);
    //     ge25519_p3_tobytes(sig, &R);

    //     _crypto_sign_ed25519_ref10_hinit(&hs, prehashed);
    //     crypto_generichash_update(&hs, sig, 64);
    //     //crypto_generichash_update(&hs, m, mlen);
    //     crypto_generichash_final(&hs, hram, 32);

    //     sc25519_reduce(hram);
    //     _crypto_sign_ed25519_clamp(az);
    //     sc25519_muladd(sig + 32, hram, az, nonce);

    //     sodium_memzero(az, sizeof az);
    //     sodium_memzero(nonce, sizeof nonce);

    //     if (siglen_p != NULL)
    //     {
    //         *siglen_p = 64U;
    //     }
    //     return 0;
}

int crypto_sign_ed25519_detached(unsigned char *sig, unsigned long long *siglen_p,
                                 const unsigned char *m, unsigned long long mlen,
                                 const unsigned char *sk)
{
    return _crypto_sign_ed25519_detached(sig, siglen_p, m, mlen, sk, 0);
}

int crypto_sign_ed25519(unsigned char *sm, unsigned long long *smlen_p,
                        const unsigned char *m, unsigned long long mlen,
                        const unsigned char *sk)
{
    unsigned long long siglen;

    memmove(sm + crypto_sign_ed25519_BYTES, m, mlen);
    /* LCOV_EXCL_START */
    if (crypto_sign_ed25519_detached(
            sm, &siglen, sm + crypto_sign_ed25519_BYTES, mlen, sk) != 0 ||
        siglen != crypto_sign_ed25519_BYTES)
    {
        if (smlen_p != NULL)
        {
            *smlen_p = 0;
        }
        memset(sm, 0, mlen + crypto_sign_ed25519_BYTES);
        return -1;
    }
    /* LCOV_EXCL_STOP */

    if (smlen_p != NULL)
    {
        *smlen_p = mlen + siglen;
    }
    return 0;
}
