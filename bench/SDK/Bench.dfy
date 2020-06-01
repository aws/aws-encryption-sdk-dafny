// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/SDK/Keyring/RawRSAKeyring.dfy"
include "../../src/SDK/Materials.dfy"
include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/StandardLibrary/UInt.dfy"
include "../../src/SDK/CMM/Defs.dfy"
include "../../src/SDK/CMM/DefaultCMM.dfy"
include "../../src/SDK/Client.dfy"
include "../../src/SDK/MessageHeader.dfy"
include "../../src/Crypto/RSAEncryption.dfy"
include "../../src/Util/UTF8.dfy"
include "../../src/StandardLibrary/Base64.dfy"
include "../../test/Util/TestUtils.dfy"

module {:extern "Bench"} Bench {
  import opened StandardLibrary
  import opened UInt = StandardLibrary.UInt
  import CMMDefs
  import DefaultCMMDef
  import RSAEncryption
  import RawRSAKeyringDef
  import Materials
  import Client = ESDKClient
  import Msg = MessageHeader
  import UTF8
  import Base64
  import TestUtils

  method Replicate(s : string, n : UInt.uint32) returns (ret : string)
	  requires |s| * n as int < UInt.UINT32_LIMIT
	  ensures |ret| == |s| * n as int && forall i :: 0 <= i < |ret| ==> ret[i] == s[i % |s|] 
  {
    if n == 0 {
      return "";
    }

    var l := |s| as UInt.uint32;
    var a := new char[l * n];
    var i := 0 as UInt.uint32;

    while i < l * n invariant 0 <= i <= l * n && forall j :: 0 <= j < i ==> a[j] == s[j % l] {
      a[i] := s[i % l];
      i := i + 1;
    }

    assert forall i :: 0 <= i < l * n ==> a[i] == s[i % l];

    return a[..];
  }

  module {:extern "Time"} Time {
    class {:extern "Timer"} Timer {
      constructor {:extern} () { }
      method {:extern} ElapsedMilliseconds() returns (a : nat)
    }
  }

  method Main() {
    var namespace :- expect UTF8.Encode("namespace");
    var name :- expect UTF8.Encode("MyKeyring");

    var ek, dk := RSAEncryption.GenerateKeyPair(2048, RSAEncryption.PKCS1);
    var keyring := new RawRSAKeyringDef.RawRSAKeyring(namespace, name, RSAEncryption.PaddingMode.PKCS1, Some(ek), Some(dk));
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var n := 1024 * 1024;

    var msg := Replicate("lorem ipsum dolor sit amet ", n);
    var msgBytes :- expect UTF8.Encode(msg);
    var originalPlaintext :- expect UTF8.Encode(msg);
    print "Plaintext size: ", |originalPlaintext|, "\n";

    var encryptionContext := TestUtils.SmallEncryptionContext(TestUtils.SmallEncryptionContextVariation.A);

    var timer := new Time.Timer();

    var encryptRequest := Client.EncryptRequest.WithCMM(msgBytes, cmm).SetEncryptionContext(encryptionContext);
    var e :- expect Client.Encrypt(encryptRequest);

    var decryptRequest := Client.DecryptRequest.WithCMM(e, cmm);
    var finalPlaintext :- expect Client.Decrypt(decryptRequest);

    var elapsed := timer.ElapsedMilliseconds();

    print elapsed, " ms\n";
    print "Match? ", (originalPlaintext == finalPlaintext), "\n";
  }
}
