// RUN: %dafny /out:./Output/TestHKDF5.exe "./TestHKDF5.dfy" "../../src/Crypto/HKDF/HKDF-extern.cs" "../../src/Util/Arrays-extern.cs" "../../lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll" /noVerify /compile:2
// RUN: cp "../../lib/BouncyCastle.1.8.5/lib/BouncyCastle.Crypto.dll" "./Output/"
// RUN: %mono ./Output/TestHKDF5.exe > "%t" && rm ./Output/TestHKDF5.exe
// RUN: %diff "%s.expect" "%t"

include "../../src/StandardLibrary/StandardLibrary.dfy"
include "../../src/Crypto/HKDF/HKDF.dfy"
include "../../src/Crypto/HKDF/HKDFSpec.dfy"

module TestHKDF5 {
  
  import opened StandardLibrary
  import opened HKDF
  import opened Digests

  method Main() {
    // Test vector 5: Test with SHA-384 and zero-length salt/info
    var tv_salt := new [][];

    var tv_ikm  := new [][ 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
                           0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b ];

    var tv_info := new[][];

    var tv_okm_desired := new[][ 0xc8, 0xc9, 0x6e, 0x71, 0x0f, 0x89, 0xb0, 0xd7, 0x99, 0x0b, 0xca,
                                 0x68, 0xbc, 0xde, 0xc8, 0xcf, 0x85, 0x40, 0x62, 0xe5, 0x4c, 0x73,
                                 0xa7, 0xab, 0xc7, 0x43, 0xfa, 0xde, 0x9b, 0x24, 0x2d, 0xaa, 0xcc,
                                 0x1c, 0xea, 0x56, 0x70, 0x41, 0x5b, 0x52, 0x84, 0x9c ];

    var okm := hkdf(HmacSHA384, tv_salt, tv_ikm, tv_info, 42);
    if okm[..] == tv_okm_desired[..] {
      print "EQUAL\n";
    } else {
      print "NOT EQUAL\n";
    }
  }
}