
#include <string.h>

//#include "crypto_hash_sha512.h"
#include "crypto_generichash.h" // switch to blake2b (generichash) for hashing in ed25519
#include "crypto_sign_ed25519.h"
#include "ref10/sign_ed25519_ref10.h"

size_t
crypto_sign_ed25519ph_statebytes(void)
{
    return sizeof(crypto_sign_ed25519ph_state);
}

size_t
crypto_sign_ed25519_bytes(void)
{
    return crypto_sign_ed25519_BYTES;
}

size_t
crypto_sign_ed25519_seedbytes(void)
{
    return crypto_sign_ed25519_SEEDBYTES;
}

size_t
crypto_sign_ed25519_publickeybytes(void)
{
    return crypto_sign_ed25519_PUBLICKEYBYTES;
}

size_t
crypto_sign_ed25519_secretkeybytes(void)
{
    return crypto_sign_ed25519_SECRETKEYBYTES;
}

size_t
crypto_sign_ed25519_messagebytes_max(void)
{
    return crypto_sign_ed25519_MESSAGEBYTES_MAX;
}

int
crypto_sign_ed25519_sk_to_seed(unsigned char *seed, const unsigned char *sk)
{
    memmove(seed, sk, crypto_sign_ed25519_SEEDBYTES);

    return 0;
}

int
crypto_sign_ed25519_sk_to_pk(unsigned char *pk, const unsigned char *sk)
{
    memmove(pk, sk + crypto_sign_ed25519_SEEDBYTES,
            crypto_sign_ed25519_PUBLICKEYBYTES);
    return 0;
}

int
crypto_sign_ed25519ph_init(crypto_sign_ed25519ph_state *state)
{
    crypto_generichash_init(&state->hs,'\0',0,crypto_generichash_BYTES);
    return 0;
}

int
crypto_sign_ed25519ph_update(crypto_sign_ed25519ph_state *state,
                             const unsigned char *m, unsigned long long mlen)
{
    return crypto_generichash_update(&state->hs, m, mlen);
}

int
crypto_sign_ed25519ph_final_create(crypto_sign_ed25519ph_state *state,
                                   unsigned char               *sig,
                                   unsigned long long          *siglen_p,
                                   const unsigned char         *sk)
{
    unsigned char ph[crypto_generichash_BYTES];

    crypto_generichash_final(&state->hs, ph, crypto_generichash_BYTES);

    return _crypto_sign_ed25519_detached(sig, siglen_p, ph, sizeof ph, sk, 1);
}

int
crypto_sign_ed25519ph_final_verify(crypto_sign_ed25519ph_state *state,
                                   unsigned char               *sig,
                                   const unsigned char         *pk)
{
    unsigned char ph[crypto_generichash_BYTES];

    crypto_generichash_final(&state->hs, ph, crypto_generichash_BYTES);

    return _crypto_sign_ed25519_verify_detached(sig, ph, sizeof ph, pk, 1);
}
