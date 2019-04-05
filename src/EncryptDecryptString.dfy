include "StandardLibrary.dfy"
include "AwsCrypto.dfy"

import opened StandardLibrary_ = StandardLibrary
type Math = Aws.Math

method Main()
{
  var arn := "arn:aws:kms:eu-west-1:796034296227:key/96c42414-b6fd-4aa7-87f3-c6cccf341dab";
  var plaintext_original := "Hello world!";
  EncryptThenDecrypt(arn, plaintext_original);
}

method EncryptThenDecrypt(arn: string, plaintext_original: string)
{
  var plaintext := StringToByteArray(plaintext_original);

  var options := Aws.InitAPI();

  var ciphertext := new byte[1024];
  var r, ciphertext_len := encrypt_string(arn, ciphertext, plaintext, plaintext.Length);
  if r != Aws.SUCCESS { return; }
  print ">> Encrypted to ciphertext of length ", ciphertext_len, "\n";

  var plaintext_result := new byte[1024];
  var plaintext_result_len;
  r, plaintext_result_len := decrypt_string(arn, plaintext_result, ciphertext, ciphertext_len);
  if r != Aws.SUCCESS { return; }
  print ">> Decrypted to plaintext of length ", plaintext_result_len, "\n";

  calc {
    plaintext_result[..plaintext_result_len];
  ==  // by postcondition of decrypt_string
    Math.Decrypt(ciphertext[..ciphertext_len]);
  ==  // by postcondition of encrypt_string
    Math.Decrypt(Math.Encrypt(plaintext[..plaintext.Length]));
  ==  { Math.GoodEncryption(plaintext[..plaintext.Length]); }
    plaintext[..plaintext.Length];
  }
  assert plaintext.Length == plaintext_result_len as int;
  assert forall i :: 0 <= i < plaintext.Length ==> plaintext[i] == plaintext_result[i];
  print ">> Decrypted plaintext matches original!\n";

  Aws.ShutdownAPI(options);
}

method encrypt_string(key_arn: string,
                      ciphertext: array<byte>,
                      plaintext: array<byte>, plaintext_len: nat)
    returns (r: Aws.Outcome, ciphertext_len: nat)
  requires ciphertext != plaintext
  requires plaintext_len <= plaintext.Length
  modifies ciphertext
  ensures r == Aws.SUCCESS ==> ciphertext_len <= ciphertext.Length
  ensures r == Aws.SUCCESS ==> ciphertext[..ciphertext_len] == Math.Encrypt(plaintext[..plaintext_len])
{
  var kms_keyring := new Aws.KmsKeyring.Build(key_arn);

  var cmm := new Aws.CryptoMaterialsManager(kms_keyring);
  kms_keyring.Release();

  var session := new Aws.Session.FromCMM(Aws.EncryptMode, cmm);
  cmm.Release();

  r := session.SetMessageSize(plaintext_len);
  if r != Aws.SUCCESS { return; }

  var plaintext_consumed;
  r, ciphertext_len, plaintext_consumed := session.Process(
    ciphertext, ciphertext.Length,
    plaintext, plaintext_len);
  if r == Aws.SUCCESS {
    assert session.IsDone();
    assert plaintext_consumed == plaintext_len;
  }
  session.Destroy();
}

method decrypt_string(key_arn: string,
                      plaintext: array<byte>,
                      ciphertext: array<byte>, ciphertext_len: nat)
    returns (r: Aws.Outcome, plaintext_len: nat)
  requires plaintext != ciphertext
  requires ciphertext_len <= ciphertext.Length
  modifies plaintext
  ensures r == Aws.SUCCESS ==> plaintext_len <= plaintext.Length
  ensures r == Aws.SUCCESS ==> plaintext[..plaintext_len] == Math.Decrypt(ciphertext[..ciphertext_len])
{
  var kms_keyring := new Aws.KmsKeyring.Build(key_arn);

  var cmm := new Aws.CryptoMaterialsManager(kms_keyring);
  kms_keyring.Release();

  var session := new Aws.Session.FromCMM(Aws.DecryptMode, cmm);
  cmm.Release();

  var ciphertext_consumed;
  r, plaintext_len, ciphertext_consumed := session.Process(
    plaintext,
    plaintext.Length,
    ciphertext,
    ciphertext_len);
  if r == Aws.SUCCESS {
    assert session.IsDone();
    assert ciphertext_consumed == ciphertext_len;
  }
  session.Destroy();
}
