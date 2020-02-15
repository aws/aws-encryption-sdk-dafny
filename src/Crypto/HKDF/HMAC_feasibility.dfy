include "HMAC.dfy"
include "../../StandardLibrary/StandardLibrary.dfy"

module HMAC_Feasibility refines HMAC {

  class HMac {
    var key: Option<seq<uint8>>
    var algorithm: HKDFAlgorithms
    var inputSoFar: seq<uint8>

    function getKey(): Option<seq<uint8>> { key }
    function getAlgorithm(): HKDFAlgorithms { algorithm }
    function getInputSoFar(): seq<uint8> { inputSoFar }

    method Init(params: CipherParameters) {
      this.inputSoFar := [];
      this.key := match params case KeyParameter(key) => Some(key);
    }

    method Update(input: seq<uint8>) {
      this.inputSoFar := this.inputSoFar + input;
    }

    method GetResult() returns (s: seq<uint8>) {
      this.inputSoFar := [];
      // The real extern actually performs the HKDF algorithm, but for feasability
      // testing, we pretend like it returns a seq of 0's of the expected size
      s := Fill(0, GetHashLength(this.algorithm) as int);
    }
  }
}
