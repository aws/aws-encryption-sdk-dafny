include "SDK/Keyring/RawRSAKeyring.dfy"
include "SDK/Materials.dfy"
include "StandardLibrary/StandardLibrary.dfy"
include "StandardLibrary/UInt.dfy"
include "SDK/CMM/Defs.dfy"
include "SDK/CMM/DefaultCMM.dfy"
include "SDK/Client.dfy"
include "SDK/MessageHeader.dfy"
include "Crypto/RSAEncryption.dfy"
include "Util/UTF8.dfy"
include "StandardLibrary/Base64.dfy"

module Main {
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

  method Replicate(s : string, n : UInt.uint32) returns (ret : string)
	  requires |s| * n as int < UInt.UINT32_LIMIT
	  ensures |ret| == |s| * n as int && forall i :: 0 <= i < |ret| ==> ret[i] == s[i % |s|] {
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
	//method {:extern} CurrentTimeMillis() returns (a : nat)
	class {:extern "Timer"} Timer {
	  constructor {:extern} () { }
      method {:extern} ElapsedMilliseconds() returns (a : nat)
	}
  }

  method Main() {
    var namespace := UTF8.Encode("namespace");
    var name := UTF8.Encode("MyKeyring");
    if name.Failure? || namespace.Failure? {
      print "Failure: hardcoded name/namespace cannot be utf8 encoded";
      return;
    }

    var ek, dk := RSAEncryption.RSA.RSAKeygen(2048, RSAEncryption.PKCS1);
    var keyring := new RawRSAKeyringDef.RawRSAKeyring(namespace.value, name.value, RSAEncryption.RSAPaddingMode.PKCS1, 2048, Some(ek), Some(dk));
    var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);

    var n := 200 * 1024;

    var msg := Replicate("lorem ipsum dolor sit amet ", n);
    var originalPlaintext := UTF8.Encode(msg).value;
    print "Plaintext size: ", |originalPlaintext|, "\n";

    var keyA, valA := UTF8.Encode("keyA").value, UTF8.Encode("valA").value;
    var encryptionContext := [(keyA, valA)];
    assert Msg.ValidAAD(encryptionContext) by {
      // To proving ValidAAD, we need to reveal the definition of ValidAAD:
      reveal Msg.ValidAAD();
      // We also need to help the verifier with proving the AADLength is small:
      calc {
        Msg.AADLength(encryptionContext);
        2 + Msg.KVPairsLength(encryptionContext, 0, 1);
        2 + 2 + |keyA| + 2 + |valA|;
      }
      assert Msg.AADLength(encryptionContext) < UINT16_LIMIT;
    }

    var timer := new Time.Timer();

    var e := Client.Encrypt(originalPlaintext, cmm, encryptionContext);
    if e.Failure? {
      print "Bad encryption :( ", e.error, "\n";
      return;
    }

    var d := Client.Decrypt(e.value, cmm);
    if d.Failure? {
      print "bad decryption: ", d.error, "\n";
      return;
    }
    var finalPlaintext := d.value;

    var elapsed := timer.ElapsedMilliseconds();

	print elapsed, " ms\n";
	print "Match? ", (originalPlaintext == finalPlaintext), "\n";
  }
}
