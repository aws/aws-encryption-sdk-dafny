// RUN: %bcdafny /out:Output/TestHKDF2.exe TestHKDF2.dfy /noVerify /compile:2
// RUN: cp %bclib Output/
// RUN: %mono ./Output/TestHKDF2.exe > "%t" && rm ./Output/TestHKDF2.exe
// RUN: %diff "%s.expect" "%t"

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Crypto/HKDF/HKDF.dfy"
include "../../src/Crypto/HKDF/HKDFSpec.dfy"

module TestHKDF2 {

  import opened StandardLibrary
  import opened HKDF
  import opened Digests

  method Main() {
    // Test vector 2: Test with SHA-256 and zero-length salt/info
    var tv_salt := None;

    var tv_ikm  := new [][ 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
                           0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b ];

    var tv_info := new[][];

    var tv_okm_desired := new[][ 0x8d, 0xa4, 0xe7, 0x75, 0xa5, 0x63, 0xc1, 0x8f, 0x71, 0x5f, 0x80,
                                 0x2a, 0x06, 0x3c, 0x5a, 0x31, 0xb8, 0xa1, 0x1f, 0x5c, 0x5e, 0xe1,
                                 0x87, 0x9e, 0xc3, 0x45, 0x4e, 0x5f, 0x3c, 0x73, 0x8d, 0x2d, 0x9d,
                                 0x20, 0x13, 0x95, 0xfa, 0xa4, 0xb6, 0x1a, 0x96, 0xc8 ];

    var okm := hkdf(HmacSHA256, tv_salt, tv_ikm, tv_info, 42);
    if okm[..] == tv_okm_desired[..] {
      print "EQUAL\n";
    } else {
      print "NOT EQUAL\n";
    }
  }
}
