
#include <string.h>

#include "crypto_generichash.h"
#include "crypto_sign_ed25519.h"
#include "sign_ed25519_ref10.h"
#include "private/ed25519_ref10.h"
#include "randombytes.h"
#include "utils.h"

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

int _crypto_sign_ed25519_detached(unsigned char *sig, unsigned long long *siglen_p,
                                  const unsigned char *m, unsigned long long mlen,
                                  const unsigned char *sk, int prehashed)
{
    crypto_generichash_state hs;
    unsigned char az[64];
    unsigned char nonce[64];
    unsigned char hram[64];
    ge25519_p3 R;

    _crypto_sign_ed25519_ref10_hinit(&hs, prehashed);

#ifdef ED25519_NONDETERMINISTIC
    memcpy(az, sk, 32);
    _crypto_sign_ed25519_synthetic_r_hv(&hs, nonce, az);
#else
    crypto_generichash(az, 32, sk, 32, '\0', 0);
    crypto_generichash_update(&hs, az + 32, 32);
#endif

    crypto_generichash_update(&hs, m, mlen);
    crypto_generichash_final(&hs, nonce, 32);

    memmove(sig + 32, sk + 32, 32);

    sc25519_reduce(nonce);
    ge25519_scalarmult_base(&R, nonce);
    ge25519_p3_tobytes(sig, &R);

    _crypto_sign_ed25519_ref10_hinit(&hs, prehashed);
    crypto_generichash_update(&hs, sig, 64);
    crypto_generichash_update(&hs, m, mlen);
    crypto_generichash_final(&hs, hram, 32);

    sc25519_reduce(hram);
    _crypto_sign_ed25519_clamp(az);
    sc25519_muladd(sig + 32, hram, az, nonce);

    sodium_memzero(az, sizeof az);
    sodium_memzero(nonce, sizeof nonce);

    if (siglen_p != NULL)
    {
        *siglen_p = 64U;
    }
    return 0;
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
