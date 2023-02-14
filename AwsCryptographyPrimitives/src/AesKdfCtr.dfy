// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


/*
Using AES-CTR to expand a single IKM into a long sequence of pseudorandom bytes
is a very well-tread path in cryptography:

The byte stream is indistinguishable from random bytes up to the
birthday bound of the AES block size.
If it weren't, it wouldn't be safe for AES-GCM etc. to use AES-CTR
for the underlying encryption of plaintext data.
There were earlier versions of SPHINCS that used AES for fast key-expansion.
NIST's comments is that AES-CTR is not a "general purpose" KDF. 
They did not remark on the appropriateness of AES-CTR as a KDF
for specialized use cases, which is what we have.

Strictly speaking, we're doing HKDF (once) for KDF Security,
then AES-CTR to expand that derived key into many keys, quickly,
for each attribute. If we tried to use HKDF for this purpose,
we'd create a very tight performance bottleneck.

Compare 1000 HKDF calls (with output length = 44 bytes
 with 1 HKDF call + AES-CTR for 44,000 bytes of output.

Is this secure?

AES-CTR is a secure PRP so long as a (nonce, key) never repeats,
up to the birthday bound of the AES block cipher.
Once you exceed this birthday bound,
an attacker may be able to perform statistical analyses on the keystream
to defeat the indistinguishable from random property we need to prove security.

At what point does this get defeated? According to the NIST documentation on AES-CTR,
the maximum number of AES blocks you can use is 2^32.
This keeps the attacker advantage in the relevant security game below 2^-32.

Our design never allows more than 2^32 AES blocks.

(HKDF, incidentally, maxes out at 255 times the size of the hash function used with HMAC.
Our design is better suited for up to a billion derived keys.)
*/

include "../Model/AwsCryptographyPrimitivesTypes.dfy"

module {:extern "AesKdfCtr"} AesKdfCtr {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyPrimitivesTypes

  // Derive 'length' bytes of new key from the key and nonce
  // by encrypting 'length' zeros with AES/CTR
  method {:extern "AesKdfCtrStream"} Stream (
    nonce: seq<uint8>,
    key: seq<uint8>,
    length: uint32
  )
    returns (res : Result<seq<uint8>, Types.OpaqueError>)
    requires |nonce| == 16
    requires |key| == 32
    ensures res.Success? ==> |res.value| == length as nat
}
