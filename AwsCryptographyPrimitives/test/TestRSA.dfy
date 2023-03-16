// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/Digest.dfy"

module TestAwsCryptographyPrimitivesRSA {
  import Aws.Cryptography.Primitives
  import opened Wrappers
  import opened StandardLibrary.UInt
  import UTF8

  const RSA_PUBLIC_2048 := "-----BEGIN PUBLIC KEY-----\n"
    + "MIIBIjANBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEAqBvECLsPdF1J5DOkaA1n\n"
    + "UrGwNT9ard3KSMaPypla/5Jhz0veCz1OSjnx35+FE3q7omHQBmKRs6XDkj4tJ5vh\n"
    + "1baw2yzgIAqW9lOXK64GiYy0maH2NfRxGbj5LhVq5T4YOkKh9D3GFbfT9/NpcsOZ\n"
    + "M2HDX8Z+M0HM3XymtcfpHk5o6QF1lbBW+rDJEcYhPN0obBufCXaasgsBRP5Ei2b5\n"
    + "18xpy9M19By1yuC9mlNcpE5v5A8fq/qLLT4s34/6dnVxKX6gIoWDzDrUNrnPe0p5\n"
    + "pqZ1SHalrELMf/liXPrf94+0cF8g1fYVGGo+MZsG5/HRngLiskP25w5smMT51U1y\n"
    + "gQIDAQAB\n"
    + "-----END PUBLIC KEY-----";

  const RSA_PUBLIC_3072 := "-----BEGIN PUBLIC KEY-----\n"
    + "MIIBojANBgkqhkiG9w0BAQEFAAOCAY8AMIIBigKCAYEAnrUonUAKKpZE+LbQfq6I\n"
    + "gAR//GNnT7L6P3LCboXu44StJtvVyAmHZXPgdkxxT1EKLFx+Tys3B7jhgno9cs67\n"
    + "Scf0pLjJAmXOVHa6881oxi5zeP0e6+KzOPugg3C+EknS2PSHTLsdTrkgZU+oUjde\n"
    + "AgRSgmWrp8aMM1WpoLmNcWC/Pi0mSziVnIzE3WhkZ2Ccetz/viRL60VHlTwNQPVa\n"
    + "7fqbcSqBxm/VjDzYvDwzmU+4GNEs5hrA2IFDxxsYZAU8HdASQM18A8W7n0Okaa4e\n"
    + "c4svyKVFkncbNCqetynLU0A5ny7I5WVXV7DNi2VMjD/mZsEt8IrwfuWSMKuIPxs/\n"
    + "Nb/4Psr7ZvbKSlaMwEpyReHvYYqM7dd6A4Y9FirnrpAPaqlfm8UFtHKQvUckxRoR\n"
    + "05kzNN2jIRJtMwGpn+40tiei7eBGMmIn41/dnkM7GOJau4BarSJMiREK1yH9hh1C\n"
    + "GbrQu6i0F9G0uBDITen9/uPX9cxK5pNHAxeWzr2UP1UzAgMBAAE=\n"
    + "-----END PUBLIC KEY-----";

  const RSA_PUBLIC_4096 := "-----BEGIN PUBLIC KEY-----\n"
    + "MIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAs86OIUN9RbdEdyQb2tGQ\n"
    + "miDmmeJaYKanLB0lfWiuO85kJK8edZyLkHIzps81qwgVSzbMCBB7QGcMyPbb3wbE\n"
    + "B4EJ32v3cuMVUs6sOvOYV4g1c1Hi1WVqnCeH+3RSFBfb7RL7SvSUmilX2tNV6uZy\n"
    + "BmMSGBJ/IMzxoHjKSFn6r1ttwov8X5DmNTyIp4qG3qyL1qhpla1bUE5Nb6uMHI2v\n"
    + "qMM+8zSPcRN40CfaQATxevNs/69++XJ+5L1nKU9fMwust1GEbtJ6cIBwAuqlyMm9\n"
    + "CnZ+tn56FEVPrUrsQX35QRNjbi0jjKI8ItkdyJ5fLixCjJ20tCo5jeL5KJ32Rjuw\n"
    + "BlB2KQrgdw5VEMrMlTJz9oozUv8GFzjtS4kx+tAsWhji5s0jry4QFYG01Q4ezVPb\n"
    + "TYdxg1Yz265EyLmF0+/ZQtO1kQc7tXHD5Gzzwyqot/UdJwlXStUGB2yEe62HQ2LT\n"
    + "9Ly3V7rUDJzO44zuFVjqchRPYWNdiYl8BVP/ak2bMtcowk06T9bo1tRf4HJWfpIM\n"
    + "GF27MXqykKHxcmOb0UfGIfI0eUtkid4gJdCxhidiILj6SHpEr+oa/Oogz01rVCdm\n"
    + "mbWmgFxmiKse8NXNQR+7qhMYX5GgdeSbp/Lg24HF9mvnd0S2wHkC86lGyQtvzrsd\n"
    + "DdUJZ2jqiKvMLdMKNFHFGGUCAwEAAQ==\n"
    + "-----END PUBLIC KEY-----";

  method {:test} RSAEncryptTests() {
    var client :- expect Primitives.AtomicPrimitives();
    var keys := client.GenerateRSAKeyPair(input := Primitives.Types.GenerateRSAKeyPairInput(lengthBits := 2048 as Primitives.Types.RSAModulusLengthBits));
    expect keys.Success?;

    BasicRSAEncryptTest(
      Primitives.Types.RSAEncryptInput(
        padding := Primitives.Types.RSAPaddingMode.OAEP_SHA256,
        publicKey := keys.value.publicKey.pem,
        // The string "asdf" as bytes
        plaintext := [ 97, 115, 100, 102 ]
      ),
      keys.value
    );
  }
  
  method {:test} GetRSAKeyModulusLength() {
    var client :- expect Primitives.AtomicPrimitives();

    // 2048

    var publicKey2048 :- expect UTF8.Encode(RSA_PUBLIC_2048);
    var length2048 :- expect client.GetRSAKeyModulusLength(
      Primitives.Types.GetRSAKeyModulusLengthInput(publicKey := publicKey2048));
    expect length2048.length == 2048;

    // 3072
    var publicKey3072 :- expect UTF8.Encode(RSA_PUBLIC_3072);
    var length3072 :- expect client.GetRSAKeyModulusLength(
      Primitives.Types.GetRSAKeyModulusLengthInput(publicKey := publicKey3072));
    expect length3072.length == 3072;

    // 4096
    var publicKey4096 :- expect UTF8.Encode(RSA_PUBLIC_4096);
    var length4096 :- expect client.GetRSAKeyModulusLength(
      Primitives.Types.GetRSAKeyModulusLengthInput(publicKey := publicKey4096));
    expect length4096.length == 4096;
  }

  method BasicRSADecryptTests(
    input: Primitives.Types.RSADecryptInput,
    expectedOutput: seq<uint8>
  ) 
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.RSADecrypt(input);

    expect output == expectedOutput;

  }
  
  method BasicRSAEncryptTest(
    input: Primitives.Types.RSAEncryptInput,
    keypair: Primitives.Types.GenerateRSAKeyPairOutput
  ) 
  {
    var client :- expect Primitives.AtomicPrimitives();
    var output :- expect client.RSAEncrypt(input);

    var decryptInput := Primitives.Types.RSADecryptInput(
      padding := input.padding,
      privateKey := keypair.privateKey.pem,
      cipherText := output
    );

    BasicRSADecryptTests(decryptInput, input.plaintext);
  }
}
