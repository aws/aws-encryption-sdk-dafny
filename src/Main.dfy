include "SDK/ToyClient.dfy"
include "SDK/Keyring/AESKeyring.dfy"
include "SDK/Keyring/RSAKeyring.dfy"
include "SDK/Keyring/MultiKeyring.dfy"
include "SDK/Keyring/Defs.dfy"
include "SDK/Common.dfy"
include "Crypto/AESEncryption.dfy"
include "Crypto/RSAEncryption.dfy"
include "Crypto/Signature.dfy"
include "Crypto/Cipher.dfy"
include "StandardLibrary/StandardLibrary.dfy"
include "SDK/CMM/DefaultCMM.dfy"

module Main {
    import opened ToyClientDef
    import AES = AESEncryption
    import RSA = RSAEncryption
    import opened Cipher
    import opened AESKeyringDef
    import K = KeyringDefs
    import opened RSAKeyringDef
    import opened StandardLibrary
    import opened MultiKeyringDef
    import opened SDKDefs
    import opened DefaultCMMDef
    import S = Signature

    method RunToyClient() {
        var ek, dk := RSA.RSA.RSAKeygen(2048, RSA.PKCS1);
        var rsa_kr := new RSAKeyring(byteseq_of_string("namespace"), byteseq_of_string("name"), RSA.PKCS1, 2048, Some(ek), Some(dk));
        var k2 := AES.AES.AESKeygen(AES_GCM_256);
        var aes_kr := new AESKeyring(byteseq_of_string("namespace"), byteseq_of_string("name2"), k2, AES_GCM_256);
        var kr_children := new K.Keyring[1](_ => rsa_kr);
        var kr := new MultiKeyring(aes_kr, kr_children);
        var cmm := new DefaultCMM.OfKeyring(kr);
        var client := new ToyClient.OfCMM(cmm);

        var msg := byteseq_of_string("hello");
        print "Message: ", msg, "\n";
        var e := client.Enc(byteseq_of_string("hello"), enc_ctx_of_strings([("keyA", "valA")]));
            // datatype Encryption = Encryption(ec : EncCtx, edks : seq<EDK>, ciphertext : seq<uint8>)
        if e.Err? {
            print "Bad encryption :( ", e.err, "\n";
            return;
        }
        var d := client.Dec(e.get);
        if d.Err? {
            print "bad decryption: ", d.err, "\n";
            return;
        }
        print "Produced ", |e.get.edks|, " EDKs \n";
        print "Decrypted to: ", d.get, "\n";
        print "AAD: ", string_of_byteseq(FlattenSortEncCtx(e.get.ec)), "\n";
    }

    method Main() {
        RunToyClient();
    }
}