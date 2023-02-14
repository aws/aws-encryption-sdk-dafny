// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../src/AesKdfCtr.dfy"

module TestAwsCryptographyPrimitivesAesKdfCtr {
  import Aws.Cryptography.Primitives
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened AesKdfCtr

  method {:test} AesKdfCtrTests() {

    var key : seq<uint8> := [138,39,30,72,206,182,214,144,245,34,28,219,204,175,198,23,132,234,125,246,130,54,251,60,137,120,166,245,0,150,79,107];
    var nonce : seq<uint8> := [66,32,73,11,207,79,97,80,11,22,236,247,42,6,222,165];
    var goal : seq<uint8> := [143,128,174,191,9,171,140,22,40,143,11,239,249,101,61,120,176,23,233,210,125,72,114,70,209,170,206,96,24,112,215,169,100,136,162,231,208,24,135,121,223,13,239,180];
    var result :- expect Stream(nonce, key, 44);
    expect |result| == 44;
    expect goal == result;

    key := [212,191,10,32,13,55,22,101,189,182,186,119,202,16,175,49,103,82,87,190,13,142,103,201,98,84,228,47,142,96,61,167];
    nonce := [135,1,132,66,198,216,26,105,47,97,246,192,186,187,54,129];
    goal := [11,154,37,42,116,143,238,68,62,135,225,71,98,224,135,18];
    result :- expect Stream(nonce, key, 16);
    expect |result| == 16;
    expect goal == result;

    key := [106,72,42,47,58,213,111,196,126,37,46,203,150,153,188,53,32,194,159,196,221,90,124,70,45,252,99,98,42,68,94,19];
    nonce := [13,247,32,159,220,254,69,218,42,110,159,42,209,244,79,232];
    goal := [150,218,139,126,166,233,178,123,229,210,40,218,141,26,127,208,124,197,212,69,251,71,73,90,47,134,46,7,215,208,194,180,174,110,1,57,16,37,16,235,93,138,25,180,85,16,229,165,238,36,56,131,247,31,64,23,249,67,153,94,23,243,69,11];
    result :- expect Stream(nonce, key, 64);
    expect |result| == 64;
    expect goal == result;
  }
  /*
  These tests wre generated with
  const crypto = require('crypto');
  function aes256ctr_stream(length, key, nonce) {
	  const aes = crypto.createCipheriv('aes-256-ctr', key, nonce)
	  const output = aes.update(Buffer.alloc(length))
	  aes.final()
	  return output
  }
  k = crypto.randomBytes(32)
  n = crypto.randomBytes(16)
  JSON.stringify(k);
  JSON.stringify(n);
  JSON.stringify(aes256ctr_stream(44, k, n));

  k = crypto.randomBytes(32)
  n = crypto.randomBytes(16)
  JSON.stringify(k);
  JSON.stringify(n);
  JSON.stringify(aes256ctr_stream(16, k, n));
 
  k = crypto.randomBytes(32)
  n = crypto.randomBytes(16)
  JSON.stringify(k);
  JSON.stringify(n);
  JSON.stringify(aes256ctr_stream(64, k, n));
  */

}
