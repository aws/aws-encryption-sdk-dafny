// Dafny program TestVectorModels.dfy compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 2.3.0.10506
// Command Line Options: TestVectorModels.dfy TestVectorExterns.cs ../../src/extern/dotnet/UTF8.cs ../../src/extern/dotnet/Random.cs ../../src/extern/dotnet/AESEncryption.cs BouncyCastle.Crypto.dll ../../src/extern/dotnet/Signature.cs ../../src/extern/dotnet/HKDF-extern.cs ../../src/extern/dotnet/Arrays-extern.cs ../../src/extern/dotnet/RSAEncryption.cs ../../src/extern/dotnet/KMS.cs AWSSDK.Core.dll AWSSDK.KeyManagementService.dll Newtonsoft.Json.dll /noVerify /compile:2
// TestVectorModels.dfy


module {:extern ""TestVectorExterns""} TestVectorModels {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8

  import KMSKeyring = KMSKeyring

  import KMSUtils = KMSUtils

  import RawAESKeyring = RawAESKeyring

  import RawRSAKeyringDef = RawRSAKeyringDef

  import RSAEncryption = RSAEncryption

  import EncryptionSuites = EncryptionSuites

  import DefaultCMMDef = DefaultCMMDef

  import Client = ESDKClient

  import Base64 = Base64
  datatype MasterKey = MasterKey(masterKeyType: string, key: Key, providerID: Option<string>, encryptionAlgorithm: Option<string>, paddingAlgorithm: Option<string>, paddingHash: Option<string>)

  datatype Key = Key(encrypt: bool, decrypt: bool, keyType: string, keyID: string, algorithm: Option<string>, bits: Option<uint16>, encoding: Option<string>, material: Option<string>, keyIndex: string)

  datatype TestCase = TestCase(testID: string, plaintext: string, ciphertext: string, masterKeys: seq<MasterKey>)

  method {:extern ""ReadFile""} ReadFile(path: string) returns (contents: Result<seq<uint8>>)
    decreases path

  method {:extern ""ParseManifest""} ParseManifest(contents: string, keyMap: map<string, Key>) returns (testCases: Result<seq<TestCase>>)
    decreases contents, keyMap

  method {:extern ""ParseKeys""} ParseKeys(contents: string) returns (keys: Result<seq<Key>>)
    decreases contents

  function method TestURIToPath(uri: string): (path: string)
    requires |uri| > 7
    decreases uri
  {
    uri[7..]
  }

  method LoadManifest(path: string, keys: map<string, Key>) returns (testCases: Result<seq<TestCase>>)
    decreases path, keys
  {
    var manifestBytes :- ReadFile(path);
    var manifestText :- UTF8.Decode(manifestBytes);
    var res := ParseManifest(manifestText, keys);
    return res;
  }

  method LoadKeys(path: string) returns (keys: Result<seq<Key>>)
    decreases path
  {
    var keysBytes :- ReadFile(path);
    var keysText :- UTF8.Decode(keysBytes);
    var res := ParseKeys(keysText);
    return res;
  }

  method Main()
  {
    var keys := LoadKeys(""keys.json"");
    if keys.Failure? {
      print keys.error;
      return;
    }
    var keyMap: map<string, Key> := map[];
    var i := 0;
    while i < |keys.value|
      decreases |keys.value| - i
    {
      keyMap := keyMap[keys.value[i].keyIndex := keys.value[i]];
      i := i + 1;
    }
    var testVectors := LoadManifest(""manifest.json"", keyMap);
    if testVectors.Failure? {
      print testVectors.error;
      return;
    }
    var j := 0;
    var failCount := 0;
    var passCount := 0;
    var skipCount := 0;
    while j < |testVectors.value|
      decreases |testVectors.value| - j
    {
      var toTest := testVectors.value[j];
      var plaintext := ReadFile(TestURIToPath(toTest.plaintext));
      if plaintext.Failure? {
        print ""Failure reading plaintext: "", plaintext.error, ""\n"";
        return;
      }
      var ciphertext := ReadFile(TestURIToPath(toTest.ciphertext));
      if ciphertext.Failure? {
        print ""Failure reading ciphertext: "", ciphertext.error, ""\n"";
        return;
      }
      var keysToTest := toTest.masterKeys;
      var allKMS := true;
      var allKMSIndex := 0;
      while allKMSIndex < |keysToTest|
        decreases |keysToTest| - allKMSIndex
      {
        if keysToTest[allKMSIndex].masterKeyType != ""aws-kms"" {
          allKMS := false;
        }
        allKMSIndex := allKMSIndex + 1;
      }
      if !allKMS {
        skipCount := skipCount + 1;
      } else {
        var masterKeyKMS := keysToTest[0];
        var clientSupplier := new KMSUtils.DefaultClientSupplier();
        var keyring := new KMSKeyring.KMSKeyring(clientSupplier, [], Some(masterKeyKMS.key.keyID), []);
        var cmm := new DefaultCMMDef.DefaultCMM.OfKeyring(keyring);
        var d := Client.Decrypt(ciphertext.value, cmm);
        if d.Failure? {
          print toTest.testID, "": FAILED\n"";
          failCount := failCount + 1;
        } else if d.value != plaintext.value {
          print toTest.testID, "": FAILED\n"";
          failCount := failCount + 1;
        } else {
          passCount := passCount + 1;
        }
      }
      j := j + 1;
    }
    print ""Passed: "", passCount, "" Failed: "", failCount, "" Skipped: "", skipCount, ""\n"";
  }
}

module {:extern ""STL""} StandardLibrary {

  import opened U = UInt
  datatype Option<T> = None | Some(get: T) {
    function method ToResult(): Result<T>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None =>
        Failure(""Option is None"")
    }

    function method GetOrElse(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None =>
        default
    }
  }

  datatype Either<S, T> = Left(left: S) | Right(right: T)

  datatype Error = IOError(msg: string) | DeserializationError(msg: string) | SerializationError(msg: string) | Error(msg: string)

  datatype Result<T> = Success(value: T) | Failure(error: string) {
    predicate method IsFailure()
      decreases this
    {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function method Extract(): T
      requires Success?
      decreases this
    {
      value
    }

    function method ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function method GetOrElse(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }
  }

  class mut<T> {
    var x: T

    constructor (y: T)
      ensures x == y
    {
      x := y;
    }

    method put(y: T)
      modifies this
      ensures x == y
    {
      x := y;
    }

    function method get(): (y: T)
      reads this
      ensures y == x
      decreases {this}
    {
      x
    }
  }

  function method RequireEqual<T(==)>(expected: T, actual: T): (r: Result<()>)
    ensures r.Success? ==> expected == actual
  {
    Require(expected == actual)
  }

  function method Require(b: bool): (r: Result<()>)
    ensures r.Success? ==> b
    decreases b
  {
    RequireWithMessage(b, ""Failed requirement"")
  }

  function method RequireWithMessage(b: bool, message: string): (r: Result<()>)
    ensures r.Success? ==> b
    decreases b, message
  {
    if b then
      Success(())
    else
      Failure(message)
  }

  function method Join<T>(ss: seq<seq<T>>, joiner: seq<T>): (s: seq<T>)
    requires 0 < |ss|
    decreases ss, joiner
  {
    if |ss| == 1 then
      ss[0]
    else
      ss[0] + joiner + Join(ss[1..], joiner)
  }

  function method Split<T(==)>(s: seq<T>, delim: T): (res: seq<seq<T>>)
    ensures delim !in s ==> res == [s]
    ensures s == [] ==> res == [[]]
    ensures 0 < |res|
    ensures forall i: int :: 0 <= i < |res| ==> delim !in res[i]
    ensures Join(res, [delim]) == s
    decreases |s|
  {
    var i: Option<nat> := Find(s, delim, 0);
    if i.Some? then
      [s[..i.get]] + Split(s[i.get + 1..], delim)
    else
      [s]
  }

  lemma /*{:_induction s}*/ WillSplitOnDelim<T>(s: seq<T>, delim: T, head: seq<T>)
    requires head < s
    requires delim !in head && s[|head|] == delim
    ensures Split(s, delim) == [head] + Split(s[|head| + 1..], delim)
    decreases s, head
  {
  }

  lemma /*{:_induction s}*/ WillNotSplitWithOutDelim<T>(s: seq<T>, delim: T)
    requires delim !in s
    ensures Split(s, delim) == [s]
    decreases s
  {
  }

  function method Find<T(==)>(s: seq<T>, c: T, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.get && index.get < |s| && s[index.get] == c && c !in s[i .. index.get]
    ensures index.None? ==> c !in s[i..]
    decreases |s| - i
  {
    if i == |s| then
      None
    else if s[i] == c then
      Some(i)
    else
      Find(s, c, i + 1)
  }

  lemma /*{:_induction s, start}*/ FindLocatesElem<T>(s: seq<T>, c: T, start: nat, hereItIs: nat)
    requires start <= hereItIs <= |s|
    requires forall i: int :: start <= i < hereItIs ==> s[i] != c
    requires hereItIs == |s| || s[hereItIs] == c
    ensures Find(s, c, start) == if hereItIs == |s| then None else Some(hereItIs)
    decreases hereItIs - start
  {
  }

  predicate StringIs8Bit(s: string)
    decreases s
  {
    forall i: int :: 
      0 <= i < |s| ==>
        s[i] < 256 as char
  }

  function Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i: int :: 0 <= i < n ==> Fill(value, n)[i] == value
    decreases n
  {
    seq(n, (_: int) => value)
  }

  method SeqToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  method StringToByteArray(s: string) returns (a: array<uint8>)
    ensures fresh(a) && a.Length <= 2 * |s|
    decreases s
  {
    a := new uint8[|s|];
    forall i: int | 0 <= i < |s| {
      a[i] := (s[i] as int % 256) as uint8;
    }
  }

  predicate method uniq<T(==)>(s: seq<T>)
    decreases s
  {
    if s == [] then
      true
    else if s[0] in s[1..] then
      false
    else
      uniq(s[1..])
  }

  lemma /*{:_induction s}*/ uniq_idxP<T>(s: seq<T>)
    ensures uniq(s) <==> forall i: int, j: int :: 0 <= i < j < |s| ==> s[i] != s[j]
    decreases s
  {
  }

  lemma {:axiom} uniq_multisetP<T>(s: seq<T>)
    ensures uniq(s) <==> forall x: T :: x in s ==> multiset(s)[x] == 1
    decreases s

  function method sum<T>(s: seq<T>, f: T -> int): int
    decreases s
  {
    if s == [] then
      0
    else
      f(s[0]) + sum(s[1..], f)
  }

  lemma {:axiom} sum_perm<T>(s: seq<T>, s': seq<T>, f: T -> int)
    requires multiset(s) == multiset(s')
    ensures sum(s, f) == sum(s', f)
    decreases s, s'

  function count<T>(s: seq<T>, x: T): int
    decreases s
  {
    if s == [] then
      0
    else
      (if s[0] == x then 1 else 0) + count(s[1..], x)
  }

  lemma /*{:_induction s}*/ count_ge0<T>(s: seq<T>, x: T)
    ensures 0 <= count(s, x)
    decreases s
  {
  }

  lemma count_nil<T>(x: T)
    ensures count([], x) == 0
  {
  }

  lemma /*{:_induction s}*/ in_count_gt0P<T>(s: seq<T>, x: T)
    ensures x in s <==> count(s, x) > 0
    decreases s
  {
  }

  lemma /*{:_induction s}*/ count_idx_gt0P<T>(s: seq<T>, i: int)
    requires 0 <= i < |s|
    ensures count(s, s[i]) > 0
    decreases s, i
  {
  }

  lemma /*{:_induction s}*/ count_eq0P<T>(s: seq<T>, x: T)
    ensures x !in s <==> count(s, x) == 0
    decreases s
  {
  }

  lemma /*{:_induction s}*/ uniq_count_le1<T>(s: seq<T>, x: T)
    requires uniq(s)
    ensures count(s, x) <= 1
    decreases s
  {
  }

  lemma /*{:_induction s}*/ multiset_seq_count<T>(s: seq<T>, x: T)
    ensures multiset(s)[x] == count(s, x)
    decreases s
  {
  }

  lemma {:axiom} multiset_seq_eq1<T>(s: seq<T>)
    requires forall i: int, j: int :: 0 <= i < j < |s| ==> s[i] != s[j]
    ensures forall x: T :: x in multiset(s) ==> multiset(s)[x] == 1
    decreases s

  lemma {:axiom} multiset_of_seq_dup<T>(s: seq<T>, i: int, j: int)
    requires 0 <= i < j < |s|
    requires s[i] == s[j]
    ensures multiset(s)[s[i]] > 1
    decreases s, i, j

  lemma multiset_of_seq_gt0P<T>(s: seq<T>, x: T)
    requires multiset(s)[x] > 0
    ensures exists i: int :: 0 <= i < |s| && s[i] == x
    decreases s
  {
  }

  lemma {:axiom} seq_dup_multset<T>(s: seq<T>, x: T)
    requires multiset(s)[x] > 1
    ensures exists i: int, j: int :: 0 <= i < j < |s| && s[i] == s[j]
    decreases s

  lemma eq_multiset_seq_memP<T>(s: seq<T>, s': seq<T>, x: T)
    requires multiset(s) == multiset(s')
    ensures (x in s) == (x in s')
    decreases s, s'
  {
  }

  function method MapSeq<S, T>(s: seq<S>, f: S ~> T): seq<T>
    requires forall i: int :: 0 <= i < |s| ==> f.requires(s[i])
    reads set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o
    decreases s
  {
    if s == [] then
      []
    else
      [f(s[0])] + MapSeq(s[1..], f)
  }

  function method FlattenSeq<T>(s: seq<seq<T>>): seq<T>
    decreases s
  {
    if s == [] then
      []
    else
      s[0] + FlattenSeq(s[1..])
  }

  predicate method uniq_fst<S(==), T(==)>(s: seq<(S, T)>)
    decreases s
  {
    uniq(MapSeq(s, (x: (S, T)) => x.0))
  }

  lemma {:axiom} uniq_fst_uniq<S, T>(s: seq<(S, T)>)
    requires uniq_fst(s)
    ensures uniq(s)
    decreases s

  lemma {:axiom} uniq_fst_idxP<S, T>(s: seq<(S, T)>)
    requires uniq_fst(s)
    ensures forall i: int, j: int :: 0 <= i < j < |s| ==> s[i].0 != s[j].0
    decreases s

  function method min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  method values<A, B>(m: map<A, B>) returns (vals: seq<B>)
    decreases m
  {
    var keys := m.Keys;
    vals := [];
    while keys != {}
      invariant |keys| + |vals| == |m.Keys|
      decreases keys
    {
      var a :| a in keys;
      keys := keys - {a};
      vals := vals + [m[a]];
    }
  }

  lemma {:axiom} eq_multiset_eq_len<T>(s: seq<T>, s': seq<T>)
    requires multiset(s) == multiset(s')
    ensures |s| == |s'|
    decreases s, s'

  predicate method UInt8Less(a: uint8, b: uint8)
    decreases a, b
  {
    a < b
  }

  predicate method NatLess(a: nat, b: nat)
    decreases a, b
  {
    a < b
  }

  predicate method IntLess(a: int, b: int)
    decreases a, b
  {
    a < b
  }

  predicate method LexicographicLessOrEqual<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    decreases a, b
  {
    exists k: int :: 
      0 <= k <= |a| &&
      LexicographicLessOrEqualAux(a, b, less, k)
  }

  predicate method LexicographicLessOrEqualAux<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool, lengthOfCommonPrefix: nat)
    requires 0 <= lengthOfCommonPrefix <= |a|
    decreases a, b, lengthOfCommonPrefix
  {
    lengthOfCommonPrefix <= |b| &&
    (forall i: int :: 
      0 <= i < lengthOfCommonPrefix ==>
        a[i] == b[i]) &&
    (lengthOfCommonPrefix == |a| || (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
  }

  predicate Trichotomous<T(!new)>(less: (T, T) -> bool)
  {
    forall t: T, t': T :: 
      less(t, t') || t == t' || less(t', t)
  }

  lemma LexPreservesTrichotomy<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trichotomous(less)
    ensures LexicographicLessOrEqual(a, b, less) || a == b || LexicographicLessOrEqual(b, a, less)
    decreases a, b
  {
  }

  function method Filter<T>(s: seq<T>, f: T -> bool): (res: seq<T>)
    ensures forall i: int :: 0 <= i < |s| && f(s[i]) ==> s[i] in res
    ensures forall i: int :: 0 <= i < |res| ==> res[i] in s && f(res[i])
    ensures |res| <= |s|
    decreases s
  {
    if |s| == 0 then
      []
    else if f(s[0]) then
      [s[0]] + Filter(s[1..], f)
    else
      Filter(s[1..], f)
  }

  lemma /*{:_induction s, s', f}*/ FilterIsDistributive<T>(s: seq<T>, s': seq<T>, f: T -> bool)
    ensures Filter(s + s', f) == Filter(s, f) + Filter(s', f)
    decreases s, s'
  {
  }

  module {:extern ""STLUInt""} UInt {
    newtype uint8 = x: int
      | 0 <= x < 256

    newtype uint16 = x: int
      | 0 <= x < 65536

    newtype int32 = x: int
      | -2147483648 <= x < 2147483648

    newtype uint32 = x: int
      | 0 <= x < 4294967296

    newtype uint64 = x: int
      | 0 <= x < 18446744073709551616

    const UINT16_LIMIT := 65536
    const UINT32_LIMIT := 4294967296

    function method UInt16ToSeq(x: uint16): seq<uint8>
      ensures |UInt16ToSeq(x)| == 2
      decreases x
    {
      var b0: uint8 := (x / 256) as uint8;
      var b1: uint8 := (x % 256) as uint8;
      [b0, b1]
    }

    function method SeqToUInt16(s: seq<uint8>): uint16
      requires |s| == 2
      decreases s
    {
      var x0: int := s[0] as int * 256;
      var x: int := x0 + s[1] as int;
      x as uint16
    }

    lemma UInt16SeqSerDeser(x: uint16)
      ensures SeqToUInt16(UInt16ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt16SeqDeserSer(s: seq<uint8>)
      requires |s| == 2
      ensures UInt16ToSeq(SeqToUInt16(s)) == s
      decreases s
    {
    }

    method UInt16ToArray(x: uint16) returns (ret: array<uint8>)
      ensures fresh(ret)
      ensures UInt16ToSeq(x) == ret[..]
      ensures ret.Length == 2
      decreases x
    {
      ret := new uint8[2];
      ret[0] := (x / 256) as uint8;
      ret[1] := (x % 256) as uint8;
    }

    function method ArrayToUInt16(a: array<uint8>): (ret: uint16)
      requires a.Length == 2
      reads a
      ensures SeqToUInt16(a[..]) == ret
      decreases {a}, a
    {
      var x0: int := a[0] as int * 256;
      var x: int := x0 + a[1] as int;
      x as uint16
    }

    function method UInt32ToSeq(x: uint32): seq<uint8>
      ensures |UInt32ToSeq(x)| == 4
      decreases x
    {
      var b0: uint8 := (x / 16777216) as uint8;
      var x0: uint32 := x - b0 as uint32 * 16777216;
      var b1: uint8 := (x0 / 65536) as uint8;
      var x1: uint32 := x0 - b1 as uint32 * 65536;
      var b2: uint8 := (x1 / 256) as uint8;
      var b3: uint8 := (x1 % 256) as uint8;
      [b0, b1, b2, b3]
    }

    function method SeqToUInt32(s: seq<uint8>): uint32
      requires |s| == 4
      decreases s
    {
      var x0: int := s[0] as int * 16777216;
      var x1: int := x0 + s[1] as int * 65536;
      var x2: int := x1 + s[2] as int * 256;
      var x: int := x2 + s[3] as int;
      x as uint32
    }

    function SeqToNat(s: seq<uint8>): nat
      decreases s
    {
      if s == [] then
        0
      else
        var last: int := |s| - 1; SeqToNat(s[..last]) * 256 + s[last] as nat
    }

    lemma /*{:_induction s}*/ SeqToNatZeroPrefix(s: seq<uint8>)
      ensures SeqToNat(s) == SeqToNat([0] + s)
      decreases s
    {
    }

    lemma /*{:_induction s}*/ SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
      requires n < UINT32_LIMIT
      requires 4 <= |s|
      requires var but4: int := |s| - 4; s[but4..] == UInt32ToSeq(n as uint32) && forall i: int :: 0 <= i < but4 ==> s[i] == 0
      ensures SeqToNat(s) == n
      decreases s, n
    {
    }

    lemma UInt32SeqSerDeser(x: uint32)
      ensures SeqToUInt32(UInt32ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt32SeqDeserSer(s: seq<uint8>)
      requires |s| == 4
      ensures UInt32ToSeq(SeqToUInt32(s)) == s
      decreases s
    {
    }

    method UInt32ToArray(x: uint32) returns (ret: array<uint8>)
      ensures fresh(ret)
      ensures UInt32ToSeq(x) == ret[..]
      ensures ret.Length == 4
      decreases x
    {
      var x' := x;
      ret := new uint8[4];
      ret[0] := (x' / 16777216) as uint8;
      x' := x' - ret[0] as uint32 * 16777216;
      ret[1] := (x' / 65536) as uint8;
      x' := x' - ret[1] as uint32 * 65536;
      ret[2] := (x' / 256) as uint8;
      ret[3] := (x' % 256) as uint8;
    }

    function method ArrayToUInt32(a: array<uint8>): (ret: uint32)
      requires a.Length == 4
      reads a
      ensures SeqToUInt32(a[..]) == ret
      decreases {a}, a
    {
      var x0: int := a[0] as int * 16777216;
      var x1: int := x0 + a[1] as int * 65536;
      var x2: int := x1 + a[2] as int * 256;
      var x: int := x2 + a[3] as int;
      x as uint32
    }

    function method {:opaque} {:fuel 0, 0} UInt64ToSeq(x: uint64): seq<uint8>
      ensures |UInt64ToSeq(x)| == 8
      decreases x
    {
      var bv: bv64 := x as bv64;
      var b0: uint8 := (bv >> 56) as uint8;
      var b1: uint8 := ((bv >> 48) & 255) as uint8;
      var b2: uint8 := ((bv >> 40) & 255) as uint8;
      var b3: uint8 := ((bv >> 32) & 255) as uint8;
      var b4: uint8 := ((bv >> 24) & 255) as uint8;
      var b5: uint8 := ((bv >> 16) & 255) as uint8;
      var b6: uint8 := ((bv >> 8) & 255) as uint8;
      var b7: uint8 := (bv & 255) as uint8;
      [b0, b1, b2, b3, b4, b5, b6, b7]
    }

    function method {:opaque} {:fuel 0, 0} SeqToUInt64(s: seq<uint8>): uint64
      requires |s| == 8
      decreases s
    {
      ((s[0] as bv64 << 56) | (s[1] as bv64 << 48) | (s[2] as bv64 << 40) | (s[3] as bv64 << 32) | (s[4] as bv64 << 24) | (s[5] as bv64 << 16) | (s[6] as bv64 << 8) | s[7] as bv64) as uint64
    }
  }
}

module {:extern ""UTF8""} UTF8 {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  type ValidUTF8Bytes = i: seq<uint8>
    | ValidUTF8Seq(i)
    witness []

  function method {:extern ""Encode""} Encode(s: string): Result<ValidUTF8Bytes>
    ensures IsASCIIString(s) ==> Encode(s).Success? && |Encode(s).value| == |s|
    decreases s

  function method {:extern ""Decode""} Decode(s: ValidUTF8Bytes): Result<string>
    decreases s

  predicate method IsASCIIString(s: string)
    decreases s
  {
    forall i: int :: 
      0 <= i < |s| ==>
        s[i] as int < 128
  }

  function method BitAt(x: uint8, idx: uint8): bool
    requires idx < 8
    decreases x, idx
  {
    var w: bv8 := x as bv8;
    (w >> idx) & 1 == 1
  }

  predicate method ValidUTF8Continuation(a: seq<uint8>, offset: nat)
    requires offset < |a|
    decreases a, offset
  {
    BitAt(a[offset], 7) &&
    !BitAt(a[offset], 6)
  }

  function method CodePointCase(a: seq<uint8>, offset: nat): uint8
    requires offset < |a|
    decreases a, offset
  {
    if BitAt(a[offset], 7) then
      if BitAt(a[offset], 6) then
        if BitAt(a[offset], 5) then
          if BitAt(a[offset], 4) then
            if BitAt(a[offset], 3) then
              0
            else
              4
          else
            3
        else
          2
      else
        0
    else
      1
  }

  predicate method ValidUTF8_at(a: seq<uint8>, offset: nat)
    requires offset <= |a|
    decreases |a| - offset
  {
    if offset == |a| then
      true
    else
      var c: uint8 := CodePointCase(a, offset); if c == 1 then ValidUTF8_at(a, offset + 1) else if c == 2 then offset + 2 <= |a| && ValidUTF8Continuation(a, offset + 1) && ValidUTF8_at(a, offset + 2) else if c == 3 then offset + 3 <= |a| && ValidUTF8Continuation(a, offset + 1) && ValidUTF8Continuation(a, offset + 2) && ValidUTF8_at(a, offset + 3) else if c == 4 then offset + 4 <= |a| && ValidUTF8Continuation(a, offset + 1) && ValidUTF8Continuation(a, offset + 2) && ValidUTF8Continuation(a, offset + 3) && ValidUTF8_at(a, offset + 4) else false
  }

  predicate method ValidUTF8(a: array<uint8>)
    reads a
    decreases {a}, a
  {
    ValidUTF8_at(a[..], 0)
  }

  predicate method ValidUTF8Seq(s: seq<uint8>)
    decreases s
  {
    ValidUTF8_at(s, 0)
  }
}

module RawAESKeyring {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import EncryptionSuites = EncryptionSuites

  import Streams = Streams

  import AlgorithmSuite = AlgorithmSuite

  import Random = Random

  import KeyringDefs = KeyringDefs

  import AESEncryption = AESEncryption

  import Mat = Materials

  import UTF8 = UTF8

  import Serialize = Serialize
  class RawAESKeyring extends KeyringDefs.Keyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const wrappingKey: seq<uint8>
    const wrappingAlgorithm: EncryptionSuites.EncryptionSuite

    predicate Valid()
      reads this
      decreases {this}
    {
      Repr == {this} &&
      |wrappingKey| == wrappingAlgorithm.keyLen as int &&
      wrappingAlgorithm in VALID_ALGORITHMS &&
      wrappingAlgorithm.Valid() &&
      |keyNamespace| < UINT16_LIMIT
    }

    constructor (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, key: seq<uint8>, wrappingAlg: EncryptionSuites.EncryptionSuite)
      requires |namespace| < UINT16_LIMIT
      requires wrappingAlg in VALID_ALGORITHMS
      requires wrappingAlg.Valid()
      requires |key| == wrappingAlg.keyLen as int
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures wrappingKey == key
      ensures wrappingAlgorithm == wrappingAlg
      ensures Valid()
      decreases namespace, name, key, wrappingAlg
    {
      keyNamespace := namespace;
      keyName := name;
      wrappingKey := key;
      wrappingAlgorithm := wrappingAlg;
      Repr := {this};
    }

    function method SerializeProviderInfo(iv: seq<uint8>): seq<uint8>
      requires Valid()
      requires |iv| == wrappingAlgorithm.ivLen as int
      reads this
      decreases {this}, iv
    {
      keyName + [0, 0, 0, wrappingAlgorithm.tagLen * 8] + [0, 0, 0, wrappingAlgorithm.ivLen] + iv
    }

    method OnEncrypt(algorithmSuiteID: Mat.AlgorithmSuite.ID, encryptionContext: Mat.EncryptionContext, plaintextDataKey: Option<seq<uint8>>)
        returns (res: Result<Option<Mat.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      ensures Valid()
      ensures unchanged(Repr)
      ensures res.Success? && res.value.Some? ==> algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==> var generateTraces: seq<KeyringTraceEntry> := Filter(res.value.get.keyringTrace, Mat.IsGenerateTraceEntry); |generateTraces| == if plaintextDataKey.None? then 1 else 0
      ensures res.Success? && res.value.Some? ==> if plaintextDataKey.None? then |res.value.get.keyringTrace| == 2 && res.value.get.keyringTrace[0] == GenerateTraceEntry() && res.value.get.keyringTrace[1] == EncryptTraceEntry() else |res.value.get.keyringTrace| == 1 && res.value.get.keyringTrace[0] == EncryptTraceEntry()
      decreases algorithmSuiteID, encryptionContext, plaintextDataKey
    {
      var keyringTrace := [];
      var plaintextDataKey := plaintextDataKey;
      if plaintextDataKey.None? {
        var k := Random.GenerateBytes(algorithmSuiteID.KeyLength() as int32);
        plaintextDataKey := Some(k);
        var generateTraceEntry := GenerateTraceEntry();
        keyringTrace := keyringTrace + [generateTraceEntry];
      }
      var iv := Random.GenerateBytes(wrappingAlgorithm.ivLen as int32);
      var aad := Mat.FlattenSortEncCtx(encryptionContext);
      var encryptResult :- AESEncryption.AESEncrypt(wrappingAlgorithm, iv, wrappingKey, plaintextDataKey.get, aad);
      var encryptedKey := encryptResult.cipherText + encryptResult.authTag;
      var providerInfo := SerializeProviderInfo(iv);
      if UINT16_LIMIT <= |providerInfo| {
        return Failure(""Serialized provider info too long."");
      }
      if UINT16_LIMIT <= |encryptedKey| {
        return Failure(""Encrypted data key too long."");
      }
      var edk := Mat.EncryptedDataKey(keyNamespace, providerInfo, encryptedKey);
      var encryptTraceEntry := EncryptTraceEntry();
      FilterIsDistributive(keyringTrace, [encryptTraceEntry], Mat.IsGenerateTraceEntry);
      FilterIsDistributive(keyringTrace, [encryptTraceEntry], Mat.IsEncryptTraceEntry);
      keyringTrace := keyringTrace + [encryptTraceEntry];
      res := Success(Some(Mat.DataKeyMaterials(algorithmSuiteID, plaintextDataKey.get, [edk], keyringTrace)));
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Mat.EncryptionContext, edks: seq<Mat.EncryptedDataKey>)
        returns (res: Result<Option<Mat.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      ensures res.Success? && res.value.Some? ==> |res.value.get.keyringTrace| == 1 && res.value.get.keyringTrace[0] == DecryptTraceEntry()
      decreases algorithmSuiteID, encryptionContext, edks
    {
      print ""I'm guessing things go wonko here\n"";
      var i := 0;
      while i < |edks|
        decreases |edks| - i
      {
        if edks[i].providerID == keyNamespace && ValidProviderInfo(edks[i].providerInfo) && wrappingAlgorithm.tagLen as int <= |edks[i].ciphertext| {
          print ""provider info: "", edks[i].providerInfo, ""\n"";
          var iv := GetIvFromProvInfo(edks[i].providerInfo);
          var wr := new Streams.StringWriter();
          var foo :- Serialize.SerializeAAD(wr, encryptionContext);
          var encCtx := wr.data[2..];
          var encryptedKeyLength := |edks[i].ciphertext| - wrappingAlgorithm.tagLen as int;
          var encryptedKey, authTag := edks[i].ciphertext[..encryptedKeyLength], edks[i].ciphertext[encryptedKeyLength..];
          var ptKey :- AESEncryption.AESDecrypt(wrappingAlgorithm, wrappingKey, encryptedKey, authTag, iv, encCtx);
          var decryptTraceEntry := DecryptTraceEntry();
          if algorithmSuiteID.ValidPlaintextDataKey(ptKey) {
            return Success(Some(Mat.OnDecryptResult(algorithmSuiteID, ptKey, [decryptTraceEntry])));
          } else {
            return Failure(""Decryption failed: bad datakey length."");
          }
        }
        i := i + 1;
      }
      return Success(None);
    }

    predicate method ValidProviderInfo(info: seq<uint8>)
      decreases info
    {
      |info| == |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN + wrappingAlgorithm.ivLen as int &&
      info[0 .. |keyName|] == keyName &&
      SeqToUInt32(info[|keyName| .. |keyName| + AUTH_TAG_LEN_LEN]) == wrappingAlgorithm.tagLen as uint32 * 8 &&
      SeqToUInt32(info[|keyName| + AUTH_TAG_LEN_LEN .. |keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN]) == wrappingAlgorithm.ivLen as uint32
    }

    function method GetIvFromProvInfo(info: seq<uint8>): seq<uint8>
      requires ValidProviderInfo(info)
      decreases info
    {
      info[|keyName| + AUTH_TAG_LEN_LEN + IV_LEN_LEN..]
    }

    function method GenerateTraceEntry(): Mat.KeyringTraceEntry
    {
      Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.GENERATED_DATA_KEY})
    }

    function method EncryptTraceEntry(): Mat.KeyringTraceEntry
    {
      Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT})
    }

    function method DecryptTraceEntry(): Mat.KeyringTraceEntry
    {
      Mat.KeyringTraceEntry(keyNamespace, keyName, {Mat.DECRYPTED_DATA_KEY, Mat.VERIFIED_ENCRYPTION_CONTEXT})
    }
  }

  const AUTH_TAG_LEN_LEN := 4
  const IV_LEN_LEN := 4
  const VALID_ALGORITHMS := {EncryptionSuites.AES_GCM_128, EncryptionSuites.AES_GCM_192, EncryptionSuites.AES_GCM_256}
}

module RawRSAKeyringDef {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import KeyringDefs = KeyringDefs

  import AlgorithmSuite = AlgorithmSuite

  import RSA = RSAEncryption

  import Materials = Materials

  import Random = Random

  import UTF8 = UTF8
  class RawRSAKeyring extends KeyringDefs.Keyring {
    const keyNamespace: UTF8.ValidUTF8Bytes
    const keyName: UTF8.ValidUTF8Bytes
    const paddingMode: RSA.RSAPaddingMode
    const bitLength: RSA.RSABitLength
    const encryptionKey: Option<seq<uint8>>
    const decryptionKey: Option<seq<uint8>>

    predicate Valid()
      reads this
      decreases {this}
    {
      Repr == {this} &&
      (encryptionKey.Some? ==>
        RSA.RSA.RSAWfEK(bitLength, paddingMode, encryptionKey.get)) &&
      (decryptionKey.Some? ==>
        RSA.RSA.RSAWfDK(bitLength, paddingMode, decryptionKey.get)) &&
      (encryptionKey.Some? || decryptionKey.Some?) &&
      |keyNamespace| < UINT16_LIMIT &&
      |keyName| < UINT16_LIMIT
    }

    constructor (namespace: UTF8.ValidUTF8Bytes, name: UTF8.ValidUTF8Bytes, padding: RSA.RSAPaddingMode, bits: RSA.RSABitLength, ek: Option<seq<uint8>>, dk: Option<seq<uint8>>)
      requires ek.Some? ==> RSA.RSA.RSAWfEK(bits, padding, ek.get)
      requires dk.Some? ==> RSA.RSA.RSAWfDK(bits, padding, dk.get)
      requires ek.Some? || dk.Some?
      requires |namespace| < UINT16_LIMIT && |name| < UINT16_LIMIT
      ensures keyNamespace == namespace
      ensures keyName == name
      ensures paddingMode == padding && bitLength == bits
      ensures encryptionKey == ek
      ensures decryptionKey == dk
      ensures Valid()
      decreases namespace, name, padding, bits, ek, dk
    {
      keyNamespace := namespace;
      keyName := name;
      paddingMode, bitLength := padding, bits;
      encryptionKey := ek;
      decryptionKey := dk;
      Repr := {this};
    }

    method OnEncrypt(algorithmSuiteID: Materials.AlgorithmSuite.ID, encryptionContext: Materials.EncryptionContext, plaintextDataKey: Option<seq<uint8>>)
        returns (res: Result<Option<Materials.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      ensures Valid()
      ensures unchanged(Repr)
      ensures res.Success? && res.value.Some? ==> algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==> var generateTraces: seq<KeyringTraceEntry> := Filter(res.value.get.keyringTrace, Materials.IsGenerateTraceEntry); |generateTraces| == if plaintextDataKey.None? then 1 else 0
      ensures res.Success? && res.value.Some? ==> if plaintextDataKey.None? then |res.value.get.keyringTrace| == 2 && res.value.get.keyringTrace[0] == GenerateTraceEntry() && res.value.get.keyringTrace[1] == EncryptTraceEntry() else |res.value.get.keyringTrace| == 1 && res.value.get.keyringTrace[0] == EncryptTraceEntry()
      decreases algorithmSuiteID, encryptionContext, plaintextDataKey
    {
      if encryptionKey.None? {
        return Failure(""Encryption key undefined"");
      } else {
        var plaintextDataKey := plaintextDataKey;
        var algorithmID := algorithmSuiteID;
        var keyringTrace := [];
        if plaintextDataKey.None? {
          var k := Random.GenerateBytes(algorithmID.KDFInputKeyLength() as int32);
          plaintextDataKey := Some(k);
          var generateTraceEntry := GenerateTraceEntry();
          keyringTrace := keyringTrace + [generateTraceEntry];
        }
        var aad := Materials.FlattenSortEncCtx(encryptionContext);
        var edkCiphertext := RSA.RSA.RSAEncrypt(bitLength, paddingMode, encryptionKey.get, plaintextDataKey.get);
        if edkCiphertext.None? {
          return Failure(""Error on encrypt!"");
        } else if UINT16_LIMIT <= |edkCiphertext.get| {
          return Failure(""Encrypted data key too long."");
        }
        var edk := Materials.EncryptedDataKey(keyNamespace, keyName, edkCiphertext.get);
        var encryptTraceEntry := EncryptTraceEntry();
        FilterIsDistributive(keyringTrace, [encryptTraceEntry], Materials.IsGenerateTraceEntry);
        FilterIsDistributive(keyringTrace, [encryptTraceEntry], Materials.IsEncryptTraceEntry);
        keyringTrace := keyringTrace + [encryptTraceEntry];
        var dataKey := Materials.DataKeyMaterials(algorithmSuiteID, plaintextDataKey.get, [edk], keyringTrace);
        assert dataKey.algorithmSuiteID.ValidPlaintextDataKey(dataKey.plaintextDataKey);
        return Success(Some(dataKey));
      }
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>)
        returns (res: Result<Option<Materials.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      ensures res.Success? && res.value.Some? ==> |res.value.get.keyringTrace| == 1 && res.value.get.keyringTrace[0] == DecryptTraceEntry()
      decreases algorithmSuiteID, encryptionContext, edks
    {
      if |edks| == 0 {
        return Success(None);
      } else if decryptionKey.None? {
        return Failure(""Decryption key undefined"");
      }
      var i := 0;
      while i < |edks|
        invariant 0 <= i <= |edks|
        decreases |edks| - i
      {
        var edk := edks[i];
        if edk.providerID != keyNamespace {
        } else if edk.providerInfo != keyName {
        } else {
          var octxt := RSA.RSA.RSADecrypt(bitLength, paddingMode, decryptionKey.get, edks[0].ciphertext);
          match octxt
          case None =>
          case Some(k) =>
            if algorithmSuiteID.ValidPlaintextDataKey(k) {
              var decryptTraceEntry := DecryptTraceEntry();
              return Success(Some(Materials.OnDecryptResult(algorithmSuiteID, k, [decryptTraceEntry])));
            } else {
              return Failure(""Bad key length!"");
            }
        }
        i := i + 1;
      }
      return Success(None);
    }

    function method GenerateTraceEntry(): Materials.KeyringTraceEntry
    {
      Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.GENERATED_DATA_KEY})
    }

    function method EncryptTraceEntry(): Materials.KeyringTraceEntry
    {
      Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.ENCRYPTED_DATA_KEY})
    }

    function method DecryptTraceEntry(): Materials.KeyringTraceEntry
    {
      Materials.KeyringTraceEntry(keyNamespace, keyName, {Materials.DECRYPTED_DATA_KEY})
    }
  }
}

module {:extern ""EncryptionSuites""} EncryptionSuites {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  datatype EncryptionAlgorithm = AES(mode: AESMode)

  datatype AESMode = GCM

  datatype EncryptionSuite = EncryptionSuite(alg: EncryptionAlgorithm, keyLen: uint8, tagLen: uint8, ivLen: uint8) {
    predicate Valid()
      decreases this
    {
      match alg
      case AES(mode) =>
        keyLen as int in AES_CIPHER_KEY_LENGTHS &&
        tagLen == AES_TAG_LEN &&
        ivLen == AES_IV_LEN &&
        mode == GCM
    }
  }

  const AES_MAX_KEY_LEN := 32
  const AES_CIPHER_KEY_LENGTHS := {32, 24, 16}
  const AES_TAG_LEN := 16 as uint8
  const AES_IV_LEN := 12 as uint8
  const AES_GCM_128 := EncryptionSuite(AES(GCM), 16, AES_TAG_LEN, AES_IV_LEN)
  const AES_GCM_192 := EncryptionSuite(AES(GCM), 24, AES_TAG_LEN, AES_IV_LEN)
  const AES_GCM_256 := EncryptionSuite(AES(GCM), 32, AES_TAG_LEN, AES_IV_LEN)
}

module {:extern ""RSAEncryption""} RSAEncryption {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  datatype {:extern ""RSAPaddingMode""} RSAPaddingMode = PKCS1 | OAEP_SHA1 | OAEP_SHA256

  newtype {:nativeType ""int""} RSABitLength = x: int
    | 521 <= x < 2147483648
    witness 521

  class {:extern ""RSA""} RSA {
    static function method msg_len_of_rsa_params(padding: RSAPaddingMode, bits: RSABitLength): Option<nat>
      decreases padding, bits
    {
      match padding {
        case PKCS1 =>
          Some(RSACoreMsgLen(bits) - 10)
        case OAEP_SHA1 =>
          Some(RSACoreMsgLen(bits) - 1 - 2 * SHA1_DIGEST_LEN)
        case OAEP_SHA256 =>
          Some(RSACoreMsgLen(bits) - 1 - 2 * SHA256_DIGEST_LEN)
      }
    }

    static predicate method {:axiom} RSAWfCtx(bits: RSABitLength, padding: RSAPaddingMode, c: seq<uint8>)
      decreases bits, padding, c

    static predicate method {:axiom} RSAWfEK(bits: RSABitLength, padding: RSAPaddingMode, ek: seq<uint8>)
      decreases bits, padding, ek

    static predicate method {:axiom} RSAWfDK(bits: RSABitLength, padding: RSAPaddingMode, dk: seq<uint8>)
      decreases bits, padding, dk

    static predicate method {:axiom} IsRSAKeypair(bits: RSABitLength, padding: RSAPaddingMode, ek: seq<uint8>, dk: seq<uint8>)
      decreases bits, padding, ek, dk

    static method {:extern ""RSAKeygen""} RSAKeygen(bits: RSABitLength, padding: RSAPaddingMode)
        returns (ek: seq<uint8>, dk: seq<uint8>)
      ensures RSAWfEK(bits, padding, ek)
      ensures RSAWfDK(bits, padding, dk)
      ensures IsRSAKeypair(bits, padding, ek, dk)
      decreases bits, padding

    static function method {:extern ""RSADecrypt""} RSADecrypt(bits: RSABitLength, padding: RSAPaddingMode, dk: seq<uint8>, c: seq<uint8>): Option<seq<uint8>>
      requires RSAWfDK(bits, padding, dk)
      decreases bits, padding, dk, c

    static method {:extern ""RSAEncrypt""} RSAEncrypt(bits: RSABitLength, padding: RSAPaddingMode, ek: seq<uint8>, msg: seq<uint8>)
        returns (c: Option<seq<uint8>>)
      requires RSAWfEK(bits, padding, ek)
      ensures c.Some? ==> RSAWfCtx(bits, padding, c.get)
      ensures c.Some? ==> forall dk: seq<uint8> :: IsRSAKeypair(bits, padding, ek, dk) ==> RSAWfDK(bits, padding, dk) ==> RSADecrypt(bits, padding, dk, c.get) == Some(msg)
      decreases bits, padding, ek, msg

    static method {:extern ""StringToPEM""} StringToPEM(privatePEM: string, publicPEM: string)
        returns (ek: seq<uint8>, dk: seq<uint8>)
      decreases privatePEM, publicPEM
  }

  function method RSACoreMsgLen(bits: RSABitLength): nat
    decreases bits
  {
    (bits as nat - 1) / 8
  }

  const SHA1_DIGEST_LEN := 20
  const SHA256_DIGEST_LEN := 32
}

module DefaultCMMDef {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Materials = Materials

  import CMMDefs = CMMDefs

  import KeyringDefs = KeyringDefs

  import AlgorithmSuite = AlgorithmSuite

  import S = Signature

  import Base64 = Base64

  import MessageHeader = MessageHeader

  import UTF8 = UTF8

  import Deserialize = Deserialize
  class DefaultCMM extends CMMDefs.CMM {
    const kr: KeyringDefs.Keyring

    predicate Valid()
      reads this, Repr
      decreases Repr + {this}
    {
      kr in Repr &&
      Repr == {this, kr} + kr.Repr &&
      kr.Valid()
    }

    constructor OfKeyring(k: KeyringDefs.Keyring)
      requires k.Valid()
      ensures kr == k
      ensures Valid()
      decreases k
    {
      kr := k;
      Repr := {this, kr} + k.Repr;
    }

    method GetEncryptionMaterials(ec: Materials.EncryptionContext, alg_id: Option<AlgorithmSuite.ID>, pt_len: Option<nat>)
        returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      requires ValidAAD(ec) && Materials.GetKeysFromEncryptionContext(ec) !! Materials.ReservedKeyValues
      ensures Valid()
      ensures res.Success? ==> res.value.dataKeyMaterials.algorithmSuiteID.ValidPlaintextDataKey(res.value.dataKeyMaterials.plaintextDataKey)
      ensures res.Success? ==> |res.value.dataKeyMaterials.encryptedDataKeys| > 0
      ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
      ensures res.Success? ==> match res.value.dataKeyMaterials.algorithmSuiteID.SignatureType() case None => true case Some(sigType) => res.value.signingKey.Some? && S.ECDSA.WfSK(sigType, res.value.signingKey.get)
      decreases ec, alg_id, pt_len
    {
      var id := if alg_id.Some? then alg_id.get else AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384;
      var enc_sk := None;
      var enc_ctx := ec;
      match id.SignatureType() {
        case None =>
        case Some(param) =>
          var oab := S.ECDSA.KeyGen(param);
          match oab
          case None =>
            return Failure(""Keygen error"");
          case Some(ab) =>
            enc_sk := Some(ab.1);
            var enc_vk :- UTF8.Encode(Base64.Encode(ab.0));
            var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
            assert reservedField in Materials.ReservedKeyValues;
            assert forall i | 0 <= i < |ec| :: ec[i].0 != reservedField;
            assert MessageHeader.SortedKVPairs(enc_ctx) by {
              assert MessageHeader.ValidAAD(enc_ctx);
              reveal MessageHeader.ValidAAD();
            }
            var optionResult;
            ghost var insertionPoint;
            optionResult, insertionPoint := Deserialize.InsertNewEntry(enc_ctx, reservedField, enc_vk);
            enc_ctx := optionResult.get;
      }
      MessageHeader.AssumeValidAAD(enc_ctx);
      var dataKeyMaterials :- kr.OnEncrypt(id, enc_ctx, None);
      if dataKeyMaterials.None? || |dataKeyMaterials.get.encryptedDataKeys| == 0 {
        return Failure(""Could not retrieve materials required for encryption"");
      }
      return Success(Materials.EncryptionMaterials(enc_ctx, dataKeyMaterials.get, enc_sk));
    }

    method DecryptMaterials(alg_id: AlgorithmSuite.ID, edks: seq<Materials.EncryptedDataKey>, enc_ctx: Materials.EncryptionContext)
        returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey)
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
      decreases alg_id, edks, enc_ctx
    {
      var vkey := None;
      if alg_id.SignatureType().Some? {
        var reservedField := Materials.EC_PUBLIC_KEY_FIELD;
        var encodedVKey := Materials.EncCtxLookup(enc_ctx, reservedField);
        if encodedVKey == None {
          return Failure(""Could not get materials required for decryption."");
        }
        var utf8Decoded :- UTF8.Decode(encodedVKey.get);
        var base64Decoded :- Base64.Decode(utf8Decoded);
        vkey := Some(base64Decoded);
      }
      var onDecryptResult :- kr.OnDecrypt(alg_id, enc_ctx, edks);
      if onDecryptResult.None? {
        return Failure(""Keyring.OnDecrypt did not return a value."");
      }
      return Success(Materials.DecryptionMaterials(alg_id, enc_ctx, onDecryptResult.get.plaintextDataKey, vkey, onDecryptResult.get.keyringTrace));
    }
  }
}

module ESDKClient {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Materials = Materials

  import AlgorithmSuite = AlgorithmSuite

  import CMMDefs = CMMDefs

  import Msg = MessageHeader

  import MessageBody = MessageBody

  import Serialize = Serialize

  import Random = Random

  import Digests = Digests

  import Streams = Streams

  import HKDF = HKDF

  import AESEncryption = AESEncryption

  import Signature = Signature

  import Deserialize = Deserialize
  method Encrypt(plaintext: seq<uint8>, cmm: CMMDefs.CMM, encryptionContext: Materials.EncryptionContext)
      returns (res: Result<seq<uint8>>)
    requires Materials.GetKeysFromEncryptionContext(encryptionContext) !! Materials.ReservedKeyValues
    requires cmm.Valid() && Msg.ValidAAD(encryptionContext)
    decreases plaintext, cmm, encryptionContext
  {
    var encMat :- cmm.GetEncryptionMaterials(encryptionContext, None, Some(|plaintext|));
    var dataKeyMaterials := encMat.dataKeyMaterials;
    if UINT16_LIMIT <= |dataKeyMaterials.encryptedDataKeys| {
      return Failure(""Number of EDKs exceeds the allowed maximum."");
    }
    var messageID: Msg.MessageID := Random.GenerateBytes(Msg.MESSAGE_ID_LEN as int32);
    var derivedDataKey := DeriveKey(dataKeyMaterials.plaintextDataKey, dataKeyMaterials.algorithmSuiteID, messageID);
    var frameLength := 4096;
    var headerBody := Msg.HeaderBody(Msg.VERSION_1, Msg.TYPE_CUSTOMER_AED, dataKeyMaterials.algorithmSuiteID, messageID, encMat.encryptionContext, Msg.EncryptedDataKeys(dataKeyMaterials.encryptedDataKeys), Msg.ContentType.Framed, dataKeyMaterials.algorithmSuiteID.IVLength() as uint8, frameLength);
    var wr := new Streams.StringWriter();
    var _ :- Serialize.SerializeHeaderBody(wr, headerBody);
    var unauthenticatedHeader := wr.data;
    var iv: seq<uint8> := seq(dataKeyMaterials.algorithmSuiteID.IVLength(), (_: int) => 0);
    var encryptionOutput :- AESEncryption.AESEncrypt(dataKeyMaterials.algorithmSuiteID.EncryptionSuite(), iv, derivedDataKey, [], unauthenticatedHeader);
    var headerAuthentication := Msg.HeaderAuthentication(iv, encryptionOutput.authTag);
    var _ :- Serialize.SerializeHeaderAuthentication(wr, headerAuthentication, dataKeyMaterials.algorithmSuiteID);
    var body :- MessageBody.EncryptMessageBody(plaintext, frameLength as int, messageID, derivedDataKey, dataKeyMaterials.algorithmSuiteID);
    var msg := wr.data + body;
    match dataKeyMaterials.algorithmSuiteID.SignatureType() {
      case None =>
      case Some(ecdsaParams) =>
        var digest := Signature.Digest(ecdsaParams, msg);
        var signResult := Signature.Sign(ecdsaParams, encMat.signingKey.get, digest);
        match signResult {
          case None =>
            return Failure(""Message signing failed"");
          case Some(bytes) =>
            msg := msg + UInt16ToSeq(|bytes| as uint16) + bytes;
        }
    }
    return Success(msg);
  }

  method DeriveKey(plaintextDataKey: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, messageID: Msg.MessageID)
      returns (derivedDataKey: seq<uint8>)
    requires |plaintextDataKey| == algorithmSuiteID.KDFInputKeyLength()
    ensures |derivedDataKey| == algorithmSuiteID.KeyLength()
    decreases plaintextDataKey, algorithmSuiteID, messageID
  {
    var whichSHA := AlgorithmSuite.Suite[algorithmSuiteID].hkdf;
    if whichSHA == Digests.HmacNOSHA {
      return plaintextDataKey;
    }
    var inputKeyMaterials := SeqToArray(plaintextDataKey);
    var infoSeq := UInt16ToSeq(algorithmSuiteID as uint16) + messageID;
    var info := SeqToArray(infoSeq);
    var len := algorithmSuiteID.KeyLength();
    var derivedKey := HKDF.hkdf(whichSHA, None, inputKeyMaterials, info, len);
    return derivedKey[..];
  }

  method Decrypt(message: seq<uint8>, cmm: CMMDefs.CMM) returns (res: Result<seq<uint8>>)
    requires cmm.Valid()
    decreases message, cmm
  {
    var rd := new Streams.StringReader.FromSeq(message);
    var header :- Deserialize.DeserializeHeader(rd);
    var decMat :- cmm.DecryptMaterials(header.body.algorithmSuiteID, header.body.encryptedDataKeys.entries, header.body.aad);
    var decryptionKey := DeriveKey(decMat.plaintextDataKey, decMat.algorithmSuiteID, header.body.messageID);
    var plaintext;
    match header.body.contentType {
      case NonFramed =>
      case Framed =>
        plaintext :- MessageBody.DecryptFramedMessageBody(rd, decMat.algorithmSuiteID, decryptionKey, header.body.frameLength as int, header.body.messageID);
    }
    match decMat.algorithmSuiteID.SignatureType() {
      case None =>
      case Some(ecdsaParams) =>
        var msg := message[..rd.pos];
        var signatureLength :- rd.ReadUInt16();
        var sig :- rd.ReadExact(signatureLength as nat);
        var digest := Signature.Digest(ecdsaParams, msg);
        var signatureVerified := Signature.Verify(ecdsaParams, decMat.verificationKey.get, digest, sig);
        if !signatureVerified {
          return Failure(""signature not verified"");
        }
    }
    if rd.Available() != 0 {
      return Failure(""message contains additional bytes at end"");
    }
    return Success(plaintext);
  }
}

module Base64 {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  newtype index = x: int
    | 0 <= x < 64

  predicate method IsBase64Char(c: char)
    decreases c
  {
    var i: int := c as int;
    i == 43 || 47 <= i <= 57 || 65 <= i <= 90 || 97 <= i <= 122
  }

  predicate method IsUnpaddedBase64String(s: string)
    decreases s
  {
    |s| % 4 == 0 &&
    forall k: char :: 
      k in s ==>
        IsBase64Char(k)
  }

  function method Base64Char(i: index): (c: char)
    ensures IsBase64Char(c)
    decreases i
  {
    if i == 63 then
      '/'
    else if i == 62 then
      '+'
    else if 52 <= i <= 61 then
      (i as int - 4) as char
    else if 26 <= i <= 51 then
      (i as int + 71) as char
    else
      (i as int + 65) as char
  }

  function method Base64Inv(c: char): (i: index)
    requires IsBase64Char(c)
    ensures Base64Char(i) == c
    decreases c
  {
    if c == '/' then
      63
    else if c == '+' then
      62
    else if 48 <= c as int <= 57 then
      (c as int + 4) as index
    else if 65 <= c as int <= 90 then
      (c as int - 65) as index
    else
      (c as int - 71) as index
  }

  function method SplitBytes(n: int): (b: (uint8, uint8, uint8))
    requires 0 <= n < 16777216
    decreases n
  {
    var n0: int := n / 65536;
    var m0: int := n - n0 * 65536;
    var n1: int := m0 / 256;
    var m1: int := m0 - n1 * 256;
    var n2: int := m1;
    assert n0 * 65536 + n1 * 256 + n2 == n;
    (n0 as uint8, n1 as uint8, n2 as uint8)
  }

  function method CombineBytes(b: (uint8, uint8, uint8)): (n: int)
    ensures 0 <= n < 16777216
    ensures SplitBytes(n) == b
    decreases b
  {
    b.0 as int * 65536 + b.1 as int * 256 + b.2 as int
  }

  function method CombineIndices(c: (index, index, index, index)): (n: int)
    ensures 0 <= n < 16777216
    decreases c
  {
    c.0 as int * 262144 + c.1 as int * 4096 + c.2 as int * 64 + c.3 as int
  }

  function method SplitIndices(n: int): (c: (index, index, index, index))
    requires 0 <= n < 16777216
    ensures CombineIndices(c) == n
    decreases n
  {
    var n0: int := n / 262144;
    var m0: int := n - n0 * 262144;
    var n1: int := m0 / 4096;
    var m1: int := m0 - n1 * 4096;
    var n2: int := m1 / 64;
    var m2: int := m1 - n2 * 64;
    var n3: int := m2;
    assert n0 * 262144 + n1 * 4096 + n2 * 64 + n3 == n;
    (n0 as index, n1 as index, n2 as index, n3 as index)
  }

  function method DecodeBlock(c: (index, index, index, index)): (b: (uint8, uint8, uint8))
    decreases c
  {
    SplitBytes(CombineIndices(c))
  }

  function method EncodeBlock(b: (uint8, uint8, uint8)): (c: (index, index, index, index))
    ensures DecodeBlock(c) == b
    decreases b
  {
    SplitIndices(CombineBytes(b))
  }

  function method DecodeRecursively(s: seq<index>): (b: seq<uint8>)
    requires |s| % 4 == 0
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    decreases s
  {
    if |s| == 0 then
      []
    else
      var d: (uint8, uint8, uint8) := DecodeBlock((s[0], s[1], s[2], s[3])); [d.0, d.1, d.2] + DecodeRecursively(s[4..])
  }

  function method EncodeRecursively(b: seq<uint8>): (s: seq<index>)
    requires |b| % 3 == 0
    ensures |s| == |b| / 3 * 4
    ensures |s| % 4 == 0
    ensures DecodeRecursively(s) == b
    decreases b
  {
    if |b| == 0 then
      []
    else
      var e: (index, index, index, index) := EncodeBlock((b[0], b[1], b[2])); [e.0, e.1, e.2, e.3] + EncodeRecursively(b[3..])
  }

  function method FromCharsToIndices(s: seq<char>): (b: seq<index>)
    requires forall k: char :: k in s ==> IsBase64Char(k)
    ensures |b| == |s|
    ensures forall k: int :: 0 <= k < |b| ==> Base64Char(b[k]) == s[k]
    decreases s
  {
    seq(|s|, (i: int) requires 0 <= i < |s| => Base64Inv(s[i]))
  }

  function method FromIndicesToChars(b: seq<index>): (s: seq<char>)
    ensures forall k: char :: k in s ==> IsBase64Char(k)
    ensures |s| == |b|
    ensures forall k: int :: 0 <= k < |s| ==> Base64Inv(s[k]) == b[k]
    ensures FromCharsToIndices(s) == b
    decreases b
  {
    seq(|b|, (i: int) requires 0 <= i < |b| => Base64Char(b[i]))
  }

  function method DecodeConverter(s: seq<char>): (b: seq<uint8>)
    requires IsUnpaddedBase64String(s)
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    decreases s
  {
    DecodeRecursively(FromCharsToIndices(s))
  }

  function method {:opaque} {:fuel 0, 0} EncodeConverter(b: seq<uint8>): (s: seq<char>)
    requires |b| % 3 == 0
    ensures IsUnpaddedBase64String(s)
    ensures |s| == |b| / 3 * 4
    ensures DecodeConverter(s) == b
    decreases b
  {
    FromIndicesToChars(EncodeRecursively(b))
  }

  predicate method Is1Padding(s: seq<char>)
    decreases s
  {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    IsBase64Char(s[2]) &&
    Base64Inv(s[2]) % 4 == 0 &&
    s[3] == '='
  }

  function method Decode1Padding(s: seq<char>): (b: seq<uint8>)
    requires Is1Padding(s)
    ensures |b| == 2
    decreases s
  {
    var c: (char, char, char, char) := (s[0], s[1], s[2], 'A');
    var d: (uint8, uint8, uint8) := DecodeBlock((Base64Inv(c.0), Base64Inv(c.1), Base64Inv(c.2), Base64Inv(c.3)));
    [d.0, d.1]
  }

  function method {:opaque} {:fuel 0, 0} Encode1Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 2
    ensures Is1Padding(s)
    ensures Decode1Padding(s) == b
    decreases b
  {
    var e: (index, index, index, index) := EncodeBlock((b[0], b[1], 0));
    [Base64Char(e.0), Base64Char(e.1), Base64Char(e.2), '=']
  }

  predicate method Is2Padding(s: seq<char>)
    decreases s
  {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    Base64Inv(s[1]) % 16 == 0 &&
    s[2] == '=' &&
    s[3] == '='
  }

  function method Decode2Padding(s: seq<char>): (b: seq<uint8>)
    requires Is2Padding(s)
    decreases s
  {
    var c: (char, char, char, char) := (s[0], s[1], 'A', 'A');
    var d: (uint8, uint8, uint8) := DecodeBlock((Base64Inv(c.0), Base64Inv(c.1), Base64Inv(c.2), Base64Inv(c.3)));
    [d.0]
  }

  function method Encode2Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 1
    ensures Is2Padding(s)
    ensures Decode2Padding(s) == b
    decreases b
  {
    var e: (index, index, index, index) := EncodeBlock((b[0], 0, 0));
    [Base64Char(e.0), Base64Char(e.1), '=', '=']
  }

  predicate method IsBase64String(s: string)
    decreases s
  {
    |s| % 4 == 0 &&
    (IsUnpaddedBase64String(s) || (IsUnpaddedBase64String(s[..|s| - 4]) && (Is2Padding(s[|s| - 4..]) || Is1Padding(s[|s| - 4..]))))
  }

  function method DecodeValid(s: seq<char>): (b: seq<uint8>)
    requires IsBase64String(s)
    decreases s
  {
    if s == [] then
      []
    else if Is2Padding(s[|s| - 4..]) then
      DecodeConverter(s[..|s| - 4]) + Decode2Padding(s[|s| - 4..])
    else if Is1Padding(s[|s| - 4..]) then
      DecodeConverter(s[..|s| - 4]) + Decode1Padding(s[|s| - 4..])
    else
      DecodeConverter(s)
  }

  function method Decode(s: seq<char>): (b: Result<seq<uint8>>)
    decreases s
  {
    if IsBase64String(s) then
      Success(DecodeValid(s))
    else
      Failure(""The encoding is malformed"")
  }

  function method Encode(b: seq<uint8>): (s: seq<char>)
    ensures Decode(s) == Success(b)
    ensures StringIs8Bit(s)
    decreases b
  {
    var res: seq<char> := if |b| % 3 == 0 then EncodeConverter(b) else if |b| % 3 == 1 then EncodeConverter(b[..|b| - 1]) + Encode2Padding(b[|b| - 1..]) else EncodeConverter(b[..|b| - 2]) + Encode1Padding(b[|b| - 2..]);
    assert DecodeValid(res) == b;
    res
  }

  method TestBase64(msg: string, expected: string)
    requires forall k: int :: 0 <= k < |msg| ==> 0 <= msg[k] as int < 256
    decreases msg, expected
  {
    print ""The message is: "", msg, ""\n"";
    var uint8Msg: seq<uint8> := [];
    var i := 0;
    while i < |msg|
      decreases |msg| - i
    {
      uint8Msg := uint8Msg + [msg[i] as int as uint8];
      i := i + 1;
    }
    var encoded := Encode(uint8Msg);
    print ""The encoding is: "", encoded, ""\n"";
    print ""The expected is: "", expected, ""\n"";
    print ""The encoding "", if encoded == expected then ""matches"" else ""doesn't match"", "" the expected.\n"";
    var decoded := Decode(encoded);
    assert decoded.value == uint8Msg;
    var dmsg := """";
    i := 0;
    while i < |decoded.value|
      decreases |decoded.value| - i
    {
      dmsg := dmsg + [decoded.value[i] as int as char];
      i := i + 1;
    }
    print ""The decoded message is: "", dmsg, ""\n\n"";
  }
}

module {:extern ""KMSUtils""} KMSUtils {

  import Mat = Materials

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8
  type CustomerMasterKey = s: string
    | ValidFormatCMK(s)
    witness ""alias/ExampleAlias""

  type GrantToken = s: string
    | 0 < |s| <= 8192
    witness ""witness""

  trait ClientSupplier {
    method GetClient(region: Option<string>) returns (res: Result<KMSClient>)
      decreases region
  }

  class DefaultClientSupplier extends ClientSupplier {
    constructor ()
    {
    }

    method {:extern} GetClient(region: Option<string>) returns (res: Result<KMSClient>)
      decreases region
  }

  datatype ResponseMetadata = ResponseMetadata(metadata: map<string, string>, requestID: string)

  type HttpStatusCode = int

  datatype GenerateDataKeyRequest = GenerateDataKeyRequest(encryptionContext: Mat.EncryptionContext, grantTokens: seq<GrantToken>, keyID: CustomerMasterKey, numberOfBytes: int32) {
    predicate Valid()
      decreases this
    {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS &&
      0 < numberOfBytes <= 1024
    }
  }

  datatype GenerateDataKeyResponse = GenerateDataKeyResponse(ciphertextBlob: seq<uint8>, contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, plaintext: seq<uint8>, responseMetadata: ResponseMetadata) {
    predicate method IsWellFormed()
      decreases this
    {
      |keyID| < UINT16_LIMIT &&
      |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype EncryptRequest = EncryptRequest(encryptionContext: Mat.EncryptionContext, grantTokens: seq<GrantToken>, keyID: CustomerMasterKey, plaintext: seq<uint8>) {
    predicate Valid()
      decreases this
    {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype EncryptResponse = EncryptResponse(ciphertextBlob: seq<uint8>, contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, responseMetadata: ResponseMetadata) {
    predicate method IsWellFormed()
      decreases this
    {
      |keyID| < UINT16_LIMIT &&
      |ciphertextBlob| < UINT16_LIMIT
    }
  }

  datatype DecryptRequest = DecryptRequest(ciphertextBlob: seq<uint8>, encryptionContext: Mat.EncryptionContext, grantTokens: seq<GrantToken>) {
    predicate Valid()
      decreases this
    {
      0 <= |grantTokens| <= MAX_GRANT_TOKENS
    }
  }

  datatype DecryptResponse = DecryptResponse(contentLength: int, httpStatusCode: HttpStatusCode, keyID: string, plaintext: seq<uint8>, responseMetadata: ResponseMetadata)

  class KMSClient {
    method {:extern} GenerateDataKey(request: GenerateDataKeyRequest) returns (res: Result<GenerateDataKeyResponse>)
      requires request.Valid()
      decreases request

    method {:extern} Encrypt(request: EncryptRequest) returns (res: Result<EncryptResponse>)
      requires request.Valid()
      decreases request

    method {:extern} Decrypt(request: DecryptRequest) returns (res: Result<DecryptResponse>)
      decreases request
  }

  const MAX_GRANT_TOKENS := 10

  predicate method ValidFormatCMK(cmk: string)
    decreases cmk
  {
    ValidFormatCMKKeyARN(cmk) || ValidFormatCMKAlias(cmk) || ValidFormatCMKAliasARN(cmk)
  }

  predicate method ValidFormatCMKKeyARN(cmk: string)
    decreases cmk
  {
    var components: seq<seq<char>> := Split(cmk, ':');
    UTF8.IsASCIIString(cmk) &&
    0 < |cmk| <= 2048 &&
    |components| == 6 &&
    components[0] == ""arn"" &&
    components[2] == ""kms"" &&
    Split(components[5], '/')[0] == ""key""
  }

  predicate method ValidFormatCMKAlias(cmk: string)
    decreases cmk
  {
    var components: seq<seq<char>> := Split(cmk, '/');
    UTF8.IsASCIIString(cmk) &&
    0 < |cmk| <= 2048 &&
    |components| == 2 &&
    components[0] == ""alias""
  }

  predicate method ValidFormatCMKAliasARN(cmk: string)
    decreases cmk
  {
    var components: seq<seq<char>> := Split(cmk, ':');
    UTF8.IsASCIIString(cmk) &&
    0 < |cmk| <= 2048 &&
    |components| == 6 &&
    components[0] == ""arn"" &&
    components[2] == ""kms"" &&
    Split(components[5], '/')[0] == ""alias""
  }
}

module KMSKeyring {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import AlgorithmSuite = AlgorithmSuite

  import KeyringDefs = KeyringDefs

  import Mat = Materials

  import KMSUtils = KMSUtils

  import UTF8 = UTF8
  class KMSKeyring extends KeyringDefs.Keyring {
    const clientSupplier: KMSUtils.ClientSupplier
    const keyIDs: seq<KMSUtils.CustomerMasterKey>
    const generator: Option<KMSUtils.CustomerMasterKey>
    const grantTokens: seq<KMSUtils.GrantToken>
    const isDiscovery: bool

    predicate Valid()
      reads this, Repr
      decreases Repr + {this}
    {
      Repr == {this} &&
      0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS &&
      (|keyIDs| == 0 &&
      generator.None? ==>
        isDiscovery)
    }

    constructor (clientSupplier: KMSUtils.ClientSupplier, keyIDs: seq<KMSUtils.CustomerMasterKey>, generator: Option<KMSUtils.CustomerMasterKey>, grantTokens: seq<KMSUtils.GrantToken>)
      requires 0 <= |grantTokens| <= KMSUtils.MAX_GRANT_TOKENS
      ensures Valid()
      decreases clientSupplier, keyIDs, generator, grantTokens
    {
      Repr := {this};
      this.clientSupplier := clientSupplier;
      this.keyIDs := keyIDs;
      this.generator := generator;
      this.grantTokens := grantTokens;
      this.isDiscovery := |keyIDs| == 0 && generator.None?;
    }

    method Generate(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Mat.EncryptionContext) returns (res: Result<Mat.ValidDataKeyMaterials>)
      requires Valid()
      requires generator.Some?
      requires !isDiscovery
      ensures Valid()
      ensures res.Success? ==> res.value.algorithmSuiteID == algorithmSuiteID && |res.value.keyringTrace| == 1 && res.value.keyringTrace[0].flags == {Mat.GENERATED_DATA_KEY, Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT}
      decreases algorithmSuiteID, encryptionContext
    {
      var generatorRequest := KMSUtils.GenerateDataKeyRequest(encryptionContext, grantTokens, generator.get, algorithmSuiteID.KDFInputKeyLength() as int32);
      var regionRes := RegionFromKMSKeyARN(generator.get);
      var regionOpt := regionRes.ToOption();
      var client :- clientSupplier.GetClient(regionOpt);
      var generatorResponse :- client.GenerateDataKey(generatorRequest);
      if !generatorResponse.IsWellFormed() {
        return Failure(""Invalid response from KMS GenerateDataKey"");
      }
      var providerInfo :- UTF8.Encode(generatorResponse.keyID);
      if UINT16_LIMIT <= |providerInfo| {
        return Failure(""providerInfo exceeds maximum length"");
      }
      var encryptedDataKey := Mat.EncryptedDataKey(PROVIDER_ID, providerInfo, generatorResponse.ciphertextBlob);
      var keyID := generatorResponse.keyID;
      var plaintextDataKey := generatorResponse.plaintext;
      if !algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) {
        return Failure(""Invalid response from KMS GenerateDataKey: Invalid key"");
      }
      var generateTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, UTF8.Encode(generator.get).value, {Mat.GENERATED_DATA_KEY, Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT});
      var datakeyMaterials := Mat.DataKeyMaterials(algorithmSuiteID, plaintextDataKey, [encryptedDataKey], [generateTraceEntry]);
      assert datakeyMaterials.Valid();
      return Success(datakeyMaterials);
    }

    method OnEncrypt(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Mat.EncryptionContext, plaintextDataKey: Option<seq<uint8>>)
        returns (res: Result<Option<Mat.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      ensures Valid()
      ensures isDiscovery ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==> var generateTraces: seq<KeyringTraceEntry> := Filter(res.value.get.keyringTrace, Mat.IsGenerateTraceEntry); |generateTraces| == if plaintextDataKey.None? then 1 else 0
      decreases algorithmSuiteID, encryptionContext, plaintextDataKey
    {
      if isDiscovery {
        return Success(None);
      } else if plaintextDataKey.None? && generator.None? {
        return Failure(""No plaintext datakey or generator defined"");
      }
      var encryptCMKs := keyIDs;
      var edks: seq<Mat.ValidEncryptedDataKey> := [];
      var keyringTrace := [];
      var ptdk: seq<uint8>;
      if generator.Some? {
        if plaintextDataKey.None? {
          var generatedMaterials :- Generate(algorithmSuiteID, encryptionContext);
          ptdk := generatedMaterials.plaintextDataKey;
          edks := generatedMaterials.encryptedDataKeys;
          keyringTrace := generatedMaterials.keyringTrace;
        } else {
          ptdk := plaintextDataKey.get;
          encryptCMKs := encryptCMKs + [generator.get];
        }
      } else {
        ptdk := plaintextDataKey.get;
      }
      var i := 0;
      while i < |encryptCMKs|
        invariant forall entry: KeyringTraceEntry :: entry in keyringTrace ==> entry.flags <= Mat.ValidEncryptionMaterialFlags
        invariant forall entry: KeyringTraceEntry :: entry in keyringTrace ==> Mat.IsGenerateTraceEntry(entry) || Mat.IsEncryptTraceEntry(entry)
        invariant |edks| == |Filter(keyringTrace, Mat.IsEncryptTraceEntry)|
        invariant |Filter(keyringTrace, Mat.IsGenerateTraceEntry)| == 1 ==> keyringTrace[0] == Filter(keyringTrace, Mat.IsGenerateTraceEntry)[0]
        invariant |Filter(keyringTrace, Mat.IsGenerateTraceEntry)| == if plaintextDataKey.None? then 1 else 0
        decreases |encryptCMKs| - i
      {
        var encryptRequest := KMSUtils.EncryptRequest(encryptionContext, grantTokens, encryptCMKs[i], ptdk);
        var regionRes := RegionFromKMSKeyARN(encryptCMKs[i]);
        var regionOpt := regionRes.ToOption();
        var client :- clientSupplier.GetClient(regionOpt);
        var encryptResponse :- client.Encrypt(encryptRequest);
        if encryptResponse.IsWellFormed() {
          var providerInfo :- UTF8.Encode(encryptResponse.keyID);
          if UINT16_LIMIT <= |providerInfo| {
            return Failure(""providerInfo exceeds maximum length"");
          }
          var edk := Mat.EncryptedDataKey(PROVIDER_ID, providerInfo, encryptResponse.ciphertextBlob);
          var encryptTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, UTF8.Encode(encryptCMKs[i]).value, {Mat.ENCRYPTED_DATA_KEY, Mat.SIGNED_ENCRYPTION_CONTEXT});
          edks := edks + [edk];
          FilterIsDistributive(keyringTrace, [encryptTraceEntry], Mat.IsGenerateTraceEntry);
          FilterIsDistributive(keyringTrace, [encryptTraceEntry], Mat.IsEncryptTraceEntry);
          keyringTrace := keyringTrace + [encryptTraceEntry];
        } else {
          return Failure(""Invalid response from KMS Encrypt"");
        }
        i := i + 1;
      }
      var datakeyMat := Mat.DataKeyMaterials(algorithmSuiteID, ptdk, edks, keyringTrace);
      assert datakeyMat.Valid();
      return Success(Some(datakeyMat));
    }

    predicate method ShouldAttemptDecryption(edk: Mat.EncryptedDataKey)
      decreases edk
    {
      var keys: seq<KMSUtils.CustomerMasterKey> := if generator.Some? then keyIDs + [generator.get] else keyIDs;
      edk.providerID == PROVIDER_ID &&
      UTF8.ValidUTF8Seq(edk.providerInfo) &&
      UTF8.Decode(edk.providerInfo).Success? &&
      KMSUtils.ValidFormatCMK(UTF8.Decode(edk.providerInfo).value) &&
      (isDiscovery || UTF8.Decode(edk.providerInfo).value in keys)
    }

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Mat.EncryptionContext, edks: seq<Mat.EncryptedDataKey>)
        returns (res: Result<Option<Mat.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      decreases algorithmSuiteID, encryptionContext, edks
    {
      if |edks| == 0 {
        return Success(None);
      }
      var i := 0;
      while i < |edks|
        decreases |edks| - i
      {
        var edk := edks[i];
        if ShouldAttemptDecryption(edk) {
          var decryptRequest := KMSUtils.DecryptRequest(edk.ciphertext, encryptionContext, grantTokens);
          var providerInfo := UTF8.Decode(edk.providerInfo).value;
          var regionRes := RegionFromKMSKeyARN(providerInfo);
          var regionOpt := regionRes.ToOption();
          var clientRes := clientSupplier.GetClient(regionOpt);
          if clientRes.Success? {
            var client := clientRes.value;
            var decryptResponseResult := client.Decrypt(decryptRequest);
            if decryptResponseResult.Success? {
              var decryptResponse := decryptResponseResult.value;
              if decryptResponse.keyID != UTF8.Decode(edk.providerInfo).value || !algorithmSuiteID.ValidPlaintextDataKey(decryptResponse.plaintext) {
                return Failure(""Invalid response from KMS Decrypt"");
              } else {
                var decryptTraceEntry := Mat.KeyringTraceEntry(PROVIDER_ID, edk.providerInfo, {Mat.DECRYPTED_DATA_KEY, Mat.VERIFIED_ENCRYPTION_CONTEXT});
                return Success(Some(Mat.OnDecryptResult(algorithmSuiteID, decryptResponse.plaintext, [decryptTraceEntry])));
              }
            }
          }
        }
        i := i + 1;
      }
      return Success(None);
    }
  }

  const PROVIDER_ID := UTF8.Encode(""aws-kms"").value

  function method RegionFromKMSKeyARN(arn: KMSUtils.CustomerMasterKey): Result<string>
    decreases arn
  {
    var components: seq<seq<char>> := Split(arn, ':');
    if 6 <= |components| && components[0] == ""arn"" && components[2] == ""kms"" then
      Success(components[3])
    else
      Failure(""Malformed ARN"")
  }
}

module AlgorithmSuite {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import EncryptionSuites = EncryptionSuites

  import S = Signature

  import Digests = Digests
  newtype ID = x: uint16
    | x in VALID_IDS
    witness 20
{
    function method EncryptionSuite(): EncryptionSuites.EncryptionSuite
      ensures EncryptionSuite().Valid()
      decreases this
    {
      Suite[this].algorithm
    }

    function method KeyLength(): nat
      decreases this
    {
      Suite[this].algorithm.keyLen as nat
    }

    function method KDFInputKeyLength(): nat
      ensures Suite[this].hkdf == Digests.HmacNOSHA ==> KDFInputKeyLength() == KeyLength()
      decreases this
    {
      KeyLength()
    }

    function method IVLength(): nat
      decreases this
    {
      Suite[this].algorithm.ivLen as nat
    }

    function method TagLength(): nat
      decreases this
    {
      Suite[this].algorithm.tagLen as nat
    }

    function method SignatureType(): Option<S.ECDSAParams>
      decreases this
    {
      Suite[this].sign
    }

    predicate method ValidPlaintextDataKey(plaintextDataKey: seq<uint8>)
      decreases this, plaintextDataKey
    {
      |plaintextDataKey| == KDFInputKeyLength()
    }
  }

  datatype AlgSuite = AlgSuite(algorithm: EncryptionSuites.EncryptionSuite, hkdf: Digests.HMAC_ALGORITHM, sign: Option<S.ECDSAParams>)

  const VALID_IDS: set<uint16> := {888, 838, 532, 376, 326, 276, 120, 70, 20}
  const AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: ID := 888
  const AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384: ID := 838
  const AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256: ID := 532
  const AES_256_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE: ID := 376
  const AES_192_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE: ID := 326
  const AES_128_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE: ID := 276
  const AES_256_GCM_IV12_TAG16_KDFNONE_SIGNONE: ID := 120
  const AES_192_GCM_IV12_TAG16_KDFNONE_SIGNONE: ID := 70
  const AES_128_GCM_IV12_TAG16_KDFNONE_SIGNONE: ID := 20
  const Suite := map[AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := AlgSuite(EncryptionSuites.AES_GCM_256, Digests.HmacSHA384, Some(S.ECDSA_P384)), AES_192_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384 := AlgSuite(EncryptionSuites.AES_GCM_192, Digests.HmacSHA384, Some(S.ECDSA_P384)), AES_128_GCM_IV12_TAG16_HKDF_SHA256_ECDSA_P256 := AlgSuite(EncryptionSuites.AES_GCM_128, Digests.HmacSHA256, Some(S.ECDSA_P256)), AES_256_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE := AlgSuite(EncryptionSuites.AES_GCM_256, Digests.HmacSHA256, None), AES_192_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE := AlgSuite(EncryptionSuites.AES_GCM_192, Digests.HmacSHA256, None), AES_128_GCM_IV12_TAG16_HKDF_SHA256_SIGNONE := AlgSuite(EncryptionSuites.AES_GCM_128, Digests.HmacSHA256, None), AES_256_GCM_IV12_TAG16_KDFNONE_SIGNONE := AlgSuite(EncryptionSuites.AES_GCM_256, Digests.HmacNOSHA, None), AES_192_GCM_IV12_TAG16_KDFNONE_SIGNONE := AlgSuite(EncryptionSuites.AES_GCM_192, Digests.HmacNOSHA, None), AES_128_GCM_IV12_TAG16_KDFNONE_SIGNONE := AlgSuite(EncryptionSuites.AES_GCM_128, Digests.HmacNOSHA, None)]

  lemma SuiteIsComplete(id: ID)
    ensures id in Suite.Keys
    decreases id
  {
  }

  lemma ValidIDsAreSuiteKeys()
    ensures VALID_IDS == set id: ID {:trigger id in Suite.Keys} | id in Suite.Keys :: id as uint16
  {
  }
}

module KeyringDefs {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Materials = Materials

  import AlgorithmSuite = AlgorithmSuite
  trait {:termination false} Keyring {
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      decreases Repr + {this}

    method OnEncrypt(algorithmSuiteID: Materials.AlgorithmSuite.ID, encryptionContext: Materials.EncryptionContext, plaintextDataKey: Option<seq<uint8>>)
        returns (res: Result<Option<Materials.ValidDataKeyMaterials>>)
      requires Valid()
      requires plaintextDataKey.Some? ==> algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey.get)
      ensures Valid()
      ensures res.Success? && res.value.Some? ==> algorithmSuiteID == res.value.get.algorithmSuiteID
      ensures res.Success? && res.value.Some? && plaintextDataKey.Some? ==> plaintextDataKey.get == res.value.get.plaintextDataKey
      ensures res.Success? && res.value.Some? ==> var generateTraces: seq<KeyringTraceEntry> := Filter(res.value.get.keyringTrace, Materials.IsGenerateTraceEntry); |generateTraces| == if plaintextDataKey.None? then 1 else 0
      decreases algorithmSuiteID, encryptionContext, plaintextDataKey

    method OnDecrypt(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: Materials.EncryptionContext, edks: seq<Materials.EncryptedDataKey>)
        returns (res: Result<Option<Materials.ValidOnDecryptResult>>)
      requires Valid()
      ensures Valid()
      ensures |edks| == 0 ==> res.Success? && res.value.None?
      ensures res.Success? && res.value.Some? ==> res.value.get.algorithmSuiteID == algorithmSuiteID
      decreases algorithmSuiteID, encryptionContext, edks
  }
}

module {:extern ""Random""} Random {

  export 
    provides GenerateBytes, UInt


  import StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  method {:extern} GenerateBytes(i: int32) returns (o: seq<uint8>)
    requires 0 <= i
    ensures |o| == i as nat
    decreases i
}

module {:extern ""AESEncryption""} AESEncryption {

  import EncryptionSuites = EncryptionSuites

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  export 
    provides AESDecrypt, AESEncrypt, EncryptionSuites, StandardLibrary, UInt
    reveals EncryptionOutput

  datatype EncryptionOutput = EncryptionOutput(cipherText: seq<uint8>, authTag: seq<uint8>)

  function method EncryptionOutputFromByteSeq(s: seq<uint8>, encAlg: EncryptionSuites.EncryptionSuite): (encArt: EncryptionOutput)
    requires encAlg.Valid()
    requires |s| >= encAlg.tagLen as int
    ensures |encArt.cipherText + encArt.authTag| == |s|
    ensures |encArt.authTag| == encAlg.tagLen as int
    decreases s, encAlg
  {
    EncryptionOutput(s[..|s| - encAlg.tagLen as int], s[|s| - encAlg.tagLen as int..])
  }

  method {:extern ""AESEncryption.AES_GCM"", ""AESEncrypt""} AESEncrypt(encAlg: EncryptionSuites.EncryptionSuite, iv: seq<uint8>, key: seq<uint8>, msg: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<EncryptionOutput>)
    requires encAlg.Valid()
    requires encAlg.alg.AES?
    requires encAlg.alg.mode.GCM?
    requires |iv| == encAlg.ivLen as int
    requires |key| == encAlg.keyLen as int
    ensures res.Success? ==> |res.value.cipherText| == |msg| && |res.value.authTag| == encAlg.tagLen as int
    decreases encAlg, iv, key, msg, aad

  method {:extern ""AESEncryption.AES_GCM"", ""AESDecrypt""} AESDecrypt(encAlg: EncryptionSuites.EncryptionSuite, key: seq<uint8>, cipherTxt: seq<uint8>, authTag: seq<uint8>, iv: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>>)
    requires encAlg.Valid()
    requires encAlg.alg.AES?
    requires encAlg.alg.mode.GCM?
    requires |key| == encAlg.keyLen as int
    requires |iv| == encAlg.ivLen as int
    requires |authTag| == encAlg.tagLen as int
    decreases encAlg, key, cipherTxt, authTag, iv, aad
}

module {:extern ""Materials""} Materials {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8

  import AlgorithmSuite = AlgorithmSuite
  type EncryptionContext = seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>

  datatype EncryptedDataKey = EncryptedDataKey(providerID: UTF8.ValidUTF8Bytes, providerInfo: seq<uint8>, ciphertext: seq<uint8>) {
    predicate Valid()
      decreases this
    {
      |providerID| < UINT16_LIMIT &&
      |providerInfo| < UINT16_LIMIT &&
      |ciphertext| < UINT16_LIMIT
    }

    static function method ValidWitness(): EncryptedDataKey
    {
      EncryptedDataKey([], [], [])
    }
  }

  type ValidEncryptedDataKey = i: EncryptedDataKey
    | i.Valid()
    witness EncryptedDataKey.ValidWitness()

  datatype KeyringTraceFlag = GENERATED_DATA_KEY | ENCRYPTED_DATA_KEY | DECRYPTED_DATA_KEY | SIGNED_ENCRYPTION_CONTEXT | VERIFIED_ENCRYPTION_CONTEXT

  datatype KeyringTraceEntry = KeyringTraceEntry(keyNamespace: UTF8.ValidUTF8Bytes, keyName: UTF8.ValidUTF8Bytes, flags: set<KeyringTraceFlag>)

  datatype DataKeyMaterials = DataKeyMaterials(algorithmSuiteID: AlgorithmSuite.ID, plaintextDataKey: seq<uint8>, encryptedDataKeys: seq<ValidEncryptedDataKey>, keyringTrace: seq<KeyringTraceEntry>) {
    predicate method Valid()
      decreases this
    {
      var generateTraces: seq<KeyringTraceEntry> := Filter(keyringTrace, IsGenerateTraceEntry);
      var encryptTraces: seq<KeyringTraceEntry> := Filter(keyringTrace, IsEncryptTraceEntry);
      algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) &&
      (forall entry: KeyringTraceEntry :: 
        entry in keyringTrace ==>
          entry.flags <= ValidEncryptionMaterialFlags) &&
      (forall entry: KeyringTraceEntry :: 
        entry in keyringTrace ==>
          IsGenerateTraceEntry(entry) || IsEncryptTraceEntry(entry)) &&
      |generateTraces| <= 1 &&
      (|generateTraces| == 1 ==>
        keyringTrace[0] == generateTraces[0]) &&
      |encryptTraces| == |encryptedDataKeys|
    }

    static function method ValidWitness(): DataKeyMaterials
    {
      DataKeyMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, seq(32, (i: int) => 0), [EncryptedDataKey.ValidWitness()], [KeyringTraceEntry([], [], {ENCRYPTED_DATA_KEY, GENERATED_DATA_KEY})])
    }
  }

  type ValidDataKeyMaterials = i: DataKeyMaterials
    | i.Valid()
    witness DataKeyMaterials.ValidWitness()

  datatype OnDecryptResult = OnDecryptResult(algorithmSuiteID: AlgorithmSuite.ID, plaintextDataKey: seq<uint8>, keyringTrace: seq<KeyringTraceEntry>) {
    predicate Valid()
      decreases this
    {
      algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) &&
      forall entry: KeyringTraceEntry :: 
        entry in keyringTrace ==>
          entry.flags <= ValidDecryptionMaterialFlags
    }

    static function method ValidWitness(): OnDecryptResult
    {
      var pdk: seq<uint8> := seq(32, (i: int) => 0);
      var entry: KeyringTraceEntry := KeyringTraceEntry([], [], {DECRYPTED_DATA_KEY});
      var r: OnDecryptResult := OnDecryptResult(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, pdk, [entry]);
      r
    }
  }

  type ValidOnDecryptResult = i: OnDecryptResult
    | i.Valid()
    witness OnDecryptResult.ValidWitness()

  datatype EncryptionMaterials = EncryptionMaterials(encryptionContext: EncryptionContext, dataKeyMaterials: ValidDataKeyMaterials, signingKey: Option<seq<uint8>>) {
    predicate method Valid()
      decreases this
    {
      true &&
      dataKeyMaterials.algorithmSuiteID.SignatureType().Some? ==>
        signingKey.Some? &&
        |dataKeyMaterials.encryptedDataKeys| > 0
    }

    static function method ValidWitness(): EncryptionMaterials
    {
      EncryptionMaterials([], DataKeyMaterials.ValidWitness(), Some(seq(32, (i: int) => 0)))
    }
  }

  type ValidEncryptionMaterials = i: EncryptionMaterials
    | i.Valid()
    witness EncryptionMaterials.ValidWitness()

  datatype DecryptionMaterials = DecryptionMaterials(algorithmSuiteID: AlgorithmSuite.ID, encryptionContext: EncryptionContext, plaintextDataKey: seq<uint8>, verificationKey: Option<seq<uint8>>, keyringTrace: seq<KeyringTraceEntry>) {
    predicate method Valid()
      decreases this
    {
      algorithmSuiteID.ValidPlaintextDataKey(plaintextDataKey) &&
      algorithmSuiteID.SignatureType().Some? ==>
        verificationKey.Some? &&
        forall entry: KeyringTraceEntry :: 
          entry in keyringTrace ==>
            entry.flags <= ValidDecryptionMaterialFlags
    }

    static function method ValidWitness(): DecryptionMaterials
    {
      DecryptionMaterials(AlgorithmSuite.AES_256_GCM_IV12_TAG16_HKDF_SHA384_ECDSA_P384, [], seq(32, (i: int) => 0), Some(seq(32, (i: int) => 0)), [KeyringTraceEntry([], [], {DECRYPTED_DATA_KEY})])
    }
  }

  type ValidDecryptionMaterials = i: DecryptionMaterials
    | i.Valid()
    witness DecryptionMaterials.ValidWitness()

  function method GetKeysFromEncryptionContext(encryptionContext: EncryptionContext): set<UTF8.ValidUTF8Bytes>
    decreases encryptionContext
  {
    set i: int {:trigger encryptionContext[i]} | 0 <= i < |encryptionContext| :: encryptionContext[i].0
  }

  const EC_PUBLIC_KEY_FIELD := UTF8.Encode(""aws-crypto-public-key"").value
  ghost const ReservedKeyValues := {EC_PUBLIC_KEY_FIELD}

  predicate method IsGenerateTraceEntry(entry: KeyringTraceEntry)
    decreases entry
  {
    GENERATED_DATA_KEY in entry.flags
  }

  predicate method IsEncryptTraceEntry(entry: KeyringTraceEntry)
    decreases entry
  {
    ENCRYPTED_DATA_KEY in entry.flags
  }

  predicate method IsDecryptTraceEntry(entry: KeyringTraceEntry)
    decreases entry
  {
    DECRYPTED_DATA_KEY in entry.flags
  }

  const ValidEncryptionMaterialFlags: set<KeyringTraceFlag> := {ENCRYPTED_DATA_KEY, SIGNED_ENCRYPTION_CONTEXT, GENERATED_DATA_KEY}
  const ValidDecryptionMaterialFlags: set<KeyringTraceFlag> := {DECRYPTED_DATA_KEY, VERIFIED_ENCRYPTION_CONTEXT}

  predicate method CompatibleDataKeyMaterials(k1: ValidDataKeyMaterials, k2: ValidDataKeyMaterials)
    decreases k1, k2
  {
    var generateTraces: seq<KeyringTraceEntry> := Filter(k1.keyringTrace + k2.keyringTrace, IsGenerateTraceEntry);
    k1.algorithmSuiteID == k2.algorithmSuiteID &&
    k1.plaintextDataKey == k2.plaintextDataKey &&
    |generateTraces| <= 1 &&
    (|generateTraces| == 1 ==>
      |k1.keyringTrace| > 0 &&
      generateTraces[0] == k1.keyringTrace[0])
  }

  function method ConcatDataKeyMaterials(k1: ValidDataKeyMaterials, k2: ValidDataKeyMaterials): (res: ValidDataKeyMaterials)
    requires CompatibleDataKeyMaterials(k1, k2)
    ensures res.algorithmSuiteID == k1.algorithmSuiteID == k2.algorithmSuiteID
    ensures res.plaintextDataKey == k1.plaintextDataKey == k2.plaintextDataKey
    ensures res.encryptedDataKeys == k1.encryptedDataKeys + k2.encryptedDataKeys
    ensures res.keyringTrace == k1.keyringTrace + k2.keyringTrace
    decreases k1, k2
  {
    FilterIsDistributive(k1.keyringTrace, k2.keyringTrace, IsEncryptTraceEntry);
    FilterIsDistributive(k1.keyringTrace, k2.keyringTrace, IsGenerateTraceEntry);
    var r: DataKeyMaterials := DataKeyMaterials(k1.algorithmSuiteID, k1.plaintextDataKey, k1.encryptedDataKeys + k2.encryptedDataKeys, k1.keyringTrace + k2.keyringTrace);
    r
  }

  function method naive_merge<T>(x: seq<T>, y: seq<T>, lt: (T, T) -> bool): seq<T>
    decreases x, y
  {
    if |x| == 0 then
      y
    else if |y| == 0 then
      x
    else if lt(x[0], y[0]) then
      [x[0]] + naive_merge(x[1..], y, lt)
    else
      [y[0]] + naive_merge(x, y[1..], lt)
  }

  function method naive_merge_sort<T>(x: seq<T>, lt: (T, T) -> bool): seq<T>
    decreases x
  {
    if |x| < 2 then
      x
    else
      var t: int := |x| / 2; naive_merge(naive_merge_sort(x[..t], lt), naive_merge_sort(x[t..], lt), lt)
  }

  function method memcmp_le(a: seq<uint8>, b: seq<uint8>, len: nat): (res: Option<bool>)
    requires |a| >= len
    requires |b| >= len
    decreases a, b, len
  {
    if len == 0 then
      None
    else if a[0] != b[0] then
      Some(a[0] < b[0])
    else
      memcmp_le(a[1..], b[1..], len - 1)
  }

  predicate method lex_lt(b: seq<uint8>, a: seq<uint8>)
    decreases b, a
  {
    match memcmp_le(a, b, if |a| < |b| then |a| else |b|) {
      case Some(b) =>
        !b
      case None =>
        !(|a| <= |b|)
    }
  }

  predicate method lt_keys(b: (seq<uint8>, seq<uint8>), a: (seq<uint8>, seq<uint8>))
    decreases b, a
  {
    lex_lt(b.0, a.0)
  }

  function method EncCtxFlatten(x: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>): UTF8.ValidUTF8Bytes
    decreases x
  {
    if x == [] then
      []
    else
      x[0].0 + x[0].1 + EncCtxFlatten(x[1..])
  }

  function method FlattenSortEncCtx(x: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>): UTF8.ValidUTF8Bytes
    decreases x
  {
    EncCtxFlatten(naive_merge_sort(x, lt_keys))
  }

  function method EncCtxLookup(x: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>, k: UTF8.ValidUTF8Bytes): Option<UTF8.ValidUTF8Bytes>
    decreases x, k
  {
    if |x| == 0 then
      None
    else if x[0].0 == k then
      Some(x[0].1)
    else
      EncCtxLookup(x[1..], k)
  }

  function method EncCtxOfStrings(x: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>): seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>
    decreases x
  {
    if x == [] then
      []
    else
      [(x[0].0, x[0].1)] + EncCtxOfStrings(x[1..])
  }
}

module Streams {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  class StringReader {
    const data: array<uint8>
    var pos: nat
    ghost var Repr: set<object>

    predicate Valid()
      reads this
      decreases {this}
    {
      this in Repr &&
      data in Repr &&
      pos <= data.Length
    }

    function method Available(): nat
      requires Valid()
      reads this
      decreases {this}
    {
      data.Length - pos
    }

    constructor (d: array<uint8>)
      ensures Valid()
      decreases d
    {
      Repr := {this, d};
      data := d;
      pos := 0;
    }

    constructor FromSeq(s: seq<uint8>)
      ensures Valid()
      ensures data[..] == s
      decreases s
    {
      var d := new uint8[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
      Repr := {this, d};
      data := d;
      pos := 0;
    }

    method Read(arr: array<uint8>, off: nat, req: nat)
        returns (res: Result<nat>)
      requires Valid() && arr != data
      requires off + req <= arr.Length
      modifies this, arr
      ensures Valid()
      ensures var n: int := min(req, old(Available())); arr[..] == arr[..off] + data[old(pos) .. old(pos) + n] + arr[off + n..]
      ensures match res case Success(lengthRead) => lengthRead == min(req, old(Available())) case Failure(e) => unchanged(this) && unchanged(arr)
      decreases arr, off, req
    {
      var n := min(req, Available());
      forall i: int | 0 <= i < n {
        arr[off + i] := data[pos + i];
      }
      pos := pos + n;
      return Success(n);
    }

    method ReadSeq(desiredByteCount: nat) returns (bytes: seq<uint8>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures bytes == data[old(pos)..][..min(desiredByteCount, old(Available()))]
      decreases desiredByteCount
    {
      var n := min(desiredByteCount, Available());
      bytes := seq(n, (i: int) requires 0 <= i < n && pos + n <= data.Length reads this, data => data[pos + i]);
      pos := pos + n;
    }

    method ReadExact(n: nat) returns (res: Result<seq<uint8>>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures match res case Success(bytes) => |bytes| == n case Failure(_) => true
      decreases n
    {
      var bytes := ReadSeq(n);
      if |bytes| != n {
        return Failure(""IO Error: Not enough bytes left on stream."");
      } else {
        return Success(bytes);
      }
    }

    method ReadByte() returns (res: Result<uint8>)
      requires Valid()
      modifies this
      ensures Valid()
    {
      var bytes :- ReadExact(1);
      var n := bytes[0];
      return Success(n);
    }

    method ReadUInt16() returns (res: Result<uint16>)
      requires Valid()
      modifies this
      ensures Valid()
    {
      var bytes :- ReadExact(2);
      var n := SeqToUInt16(bytes);
      return Success(n);
    }

    method ReadUInt32() returns (res: Result<uint32>)
      requires Valid()
      modifies this
      ensures Valid()
    {
      var bytes :- ReadExact(4);
      var n := SeqToUInt32(bytes);
      return Success(n);
    }
  }

  class StringWriter {
    var data: seq<uint8>
    ghost var Repr: set<object>

    predicate Valid()
      reads this
      decreases {this}
    {
      this in Repr
    }

    predicate method HasRemainingCapacity(n: nat)
      requires Valid()
      reads this
      decreases {this}, n
    {
      true
    }

    constructor ()
      ensures Valid() && fresh(Repr)
    {
      data := [];
      Repr := {this};
    }

    method Write(a: array<uint8>, off: nat, len: nat)
        returns (res: Result<nat>)
      requires Valid() && a !in Repr
      requires off + len <= a.Length
      modifies `data
      ensures Valid()
      ensures match res case Success(lengthWritten) => old(HasRemainingCapacity(len)) && lengthWritten == len && data == old(data) + a[off..][..len] case Failure(e) => unchanged(`data)
      decreases a, off, len
    {
      if HasRemainingCapacity(len) {
        data := data + a[off .. off + len];
        return Success(len);
      } else {
        return Failure(""IO Error: Stream capacity exceeded."");
      }
    }

    method WriteSeq(bytes: seq<uint8>) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res case Success(lengthWritten) => old(HasRemainingCapacity(|bytes|)) && lengthWritten == |bytes| && data == old(data) + bytes case Failure(e) => unchanged(`data)
      decreases bytes
    {
      if HasRemainingCapacity(|bytes|) {
        data := data + bytes;
        return Success(|bytes|);
      } else {
        return Failure(""IO Error: Stream capacity exceeded."");
      }
    }

    method WriteByte(n: uint8) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res case Success(lengthWritten) => old(HasRemainingCapacity(1)) && lengthWritten == 1 && data == old(data) + [n] case Failure(e) => unchanged(`data)
      decreases n
    {
      if HasRemainingCapacity(1) {
        data := data + [n];
        return Success(1);
      } else {
        return Failure(""IO Error: Stream capacity exceeded."");
      }
    }

    method WriteUInt16(n: uint16) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res case Success(lengthWritten) => old(HasRemainingCapacity(2)) && lengthWritten == 2 && data == old(data) + UInt16ToSeq(n) case Failure(e) => unchanged(`data)
      decreases n
    {
      if HasRemainingCapacity(2) {
        data := data + UInt16ToSeq(n);
        return Success(2);
      } else {
        return Failure(""IO Error: Stream capacity exceeded."");
      }
    }

    method WriteUInt32(n: uint32) returns (res: Result<nat>)
      requires Valid()
      modifies `data
      ensures Valid()
      ensures match res case Success(lengthWritten) => old(HasRemainingCapacity(4)) && lengthWritten == 4 && data == old(data) + UInt32ToSeq(n) case Failure(e) => unchanged(`data)
      decreases n
    {
      if HasRemainingCapacity(4) {
        data := data + UInt32ToSeq(n);
        return Success(4);
      } else {
        return Failure(""IO Error: Stream capacity exceeded."");
      }
    }
  }
}

module Serialize {

  import Msg = MessageHeader

  import AlgorithmSuite = AlgorithmSuite

  import Streams = Streams

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Materials = Materials
  method SerializeHeaderBody(wr: Streams.StringWriter, hb: Msg.HeaderBody) returns (ret: Result<nat>)
    requires wr.Valid() && hb.Valid()
    modifies wr`data
    ensures wr.Valid()
    ensures match ret case Success(totalWritten) => (var serHb := (reveal Msg.HeaderBodyToSeq(); Msg.HeaderBodyToSeq(hb)); var initLen := old(|wr.data|); totalWritten == |serHb| && initLen + totalWritten == |wr.data| && serHb == wr.data[initLen .. initLen + totalWritten]) case Failure(e) => true
    decreases wr, hb
  {
    var totalWritten := 0;
    var len :- wr.WriteByte(hb.version as uint8);
    totalWritten := totalWritten + len;
    len :- wr.WriteByte(hb.typ as uint8);
    totalWritten := totalWritten + len;
    len :- wr.WriteUInt16(hb.algorithmSuiteID as uint16);
    totalWritten := totalWritten + len;
    len :- wr.WriteSeq(hb.messageID);
    totalWritten := totalWritten + len;
    len :- SerializeAAD(wr, hb.aad);
    totalWritten := totalWritten + len;
    len :- SerializeEDKs(wr, hb.encryptedDataKeys);
    totalWritten := totalWritten + len;
    var contentType := Msg.ContentTypeToUInt8(hb.contentType);
    len :- wr.WriteByte(contentType);
    totalWritten := totalWritten + len;
    len :- wr.WriteSeq(Msg.Reserved);
    totalWritten := totalWritten + len;
    len :- wr.WriteByte(hb.ivLength);
    totalWritten := totalWritten + len;
    len :- wr.WriteUInt32(hb.frameLength);
    totalWritten := totalWritten + len;
    reveal Msg.HeaderBodyToSeq();
    return Success(totalWritten);
  }

  method SerializeHeaderAuthentication(wr: Streams.StringWriter, ha: Msg.HeaderAuthentication, ghost algorithmSuiteID: AlgorithmSuite.ID)
      returns (ret: Result<nat>)
    requires wr.Valid()
    modifies wr`data
    ensures wr.Valid()
    ensures match ret case Success(totalWritten) => (var serHa := ha.iv + ha.authenticationTag; var initLen := old(|wr.data|); initLen + totalWritten == |wr.data| && serHa == wr.data[initLen .. initLen + totalWritten] && totalWritten == |serHa|) case Failure(e) => true
    decreases wr, ha, algorithmSuiteID
  {
    var m :- wr.WriteSeq(ha.iv);
    var n :- wr.WriteSeq(ha.authenticationTag);
    return Success(m + n);
  }

  method SerializeAAD(wr: Streams.StringWriter, kvPairs: Materials.EncryptionContext) returns (ret: Result<nat>)
    requires wr.Valid() && Msg.ValidAAD(kvPairs)
    modifies wr`data
    ensures wr.Valid() && Msg.ValidAAD(kvPairs)
    ensures match ret case Success(totalWritten) => (var serAAD := Msg.AADToSeq(kvPairs); var initLen := old(|wr.data|); totalWritten == |serAAD| && initLen + totalWritten == |wr.data| && wr.data == old(wr.data) + serAAD) case Failure(e) => true
    decreases wr, kvPairs
  {
    reveal Msg.ValidAAD();
    var totalWritten := 0;
    var aadLength :- ComputeAADLength(kvPairs);
    var len :- wr.WriteUInt16(aadLength);
    totalWritten := totalWritten + len;
    if aadLength == 0 {
      return Success(totalWritten);
    }
    len :- wr.WriteUInt16(|kvPairs| as uint16);
    totalWritten := totalWritten + len;
    var j := 0;
    ghost var n := |kvPairs|;
    while j < |kvPairs|
      invariant j <= n == |kvPairs|
      invariant wr.data == old(wr.data) + UInt16ToSeq(aadLength) + UInt16ToSeq(n as uint16) + Msg.KVPairsToSeq(kvPairs, 0, j)
      invariant totalWritten == 4 + |Msg.KVPairsToSeq(kvPairs, 0, j)|
      decreases |kvPairs| - j
    {
      len :- wr.WriteUInt16(|kvPairs[j].0| as uint16);
      totalWritten := totalWritten + len;
      len :- wr.WriteSeq(kvPairs[j].0);
      totalWritten := totalWritten + len;
      len :- wr.WriteUInt16(|kvPairs[j].1| as uint16);
      totalWritten := totalWritten + len;
      len :- wr.WriteSeq(kvPairs[j].1);
      totalWritten := totalWritten + len;
      j := j + 1;
    }
    return Success(totalWritten);
  }

  method ComputeAADLength(kvPairs: Materials.EncryptionContext) returns (res: Result<uint16>)
    requires |kvPairs| < UINT16_LIMIT
    requires forall i: int :: 0 <= i < |kvPairs| ==> Msg.ValidKVPair(kvPairs[i])
    ensures match res case Success(len) => len as int == Msg.AADLength(kvPairs) case Failure(_) => UINT16_LIMIT <= Msg.AADLength(kvPairs)
    decreases kvPairs
  {
    var n: int32 := |kvPairs| as int32;
    if n == 0 {
      return Success(0);
    } else {
      var len: int32, limit: int32 := 2, UINT16_LIMIT as int32;
      var i: int32 := 0;
      while i < n
        invariant i <= n
        invariant 2 + Msg.KVPairsLength(kvPairs, 0, i as int) == len as int < UINT16_LIMIT
        decreases n as int - i as int
      {
        var kvPair := kvPairs[i];
        len := len + 4 + |kvPair.0| as int32 + |kvPair.1| as int32;
        Msg.KVPairsLengthSplit(kvPairs, 0, i as int + 1, n as int);
        if limit <= len {
          return Failure(""The number of bytes in encryption context exceeds the allowed maximum"");
        }
        i := i + 1;
      }
      return Success(len as uint16);
    }
  }

  method SerializeEDKs(wr: Streams.StringWriter, encryptedDataKeys: Msg.EncryptedDataKeys) returns (ret: Result<nat>)
    requires wr.Valid() && encryptedDataKeys.Valid()
    modifies wr`data
    ensures wr.Valid() && encryptedDataKeys.Valid()
    ensures match ret case Success(totalWritten) => (var serEDK := Msg.EDKsToSeq(encryptedDataKeys); var initLen := old(|wr.data|); totalWritten == |serEDK| && initLen + totalWritten == |wr.data| && wr.data == old(wr.data) + serEDK) case Failure(e) => true
    decreases wr, encryptedDataKeys
  {
    var totalWritten := 0;
    var len :- wr.WriteUInt16(|encryptedDataKeys.entries| as uint16);
    totalWritten := totalWritten + len;
    var j := 0;
    ghost var n := |encryptedDataKeys.entries|;
    while j < |encryptedDataKeys.entries|
      invariant j <= n == |encryptedDataKeys.entries|
      invariant wr.data == old(wr.data) + UInt16ToSeq(n as uint16) + Msg.EDKEntriesToSeq(encryptedDataKeys.entries, 0, j)
      invariant totalWritten == 2 + |Msg.EDKEntriesToSeq(encryptedDataKeys.entries, 0, j)|
      decreases |encryptedDataKeys.entries| - j
    {
      var entry := encryptedDataKeys.entries[j];
      len :- wr.WriteUInt16(|entry.providerID| as uint16);
      totalWritten := totalWritten + len;
      len :- wr.WriteSeq(entry.providerID);
      totalWritten := totalWritten + len;
      len :- wr.WriteUInt16(|entry.providerInfo| as uint16);
      totalWritten := totalWritten + len;
      len :- wr.WriteSeq(entry.providerInfo);
      totalWritten := totalWritten + len;
      len :- wr.WriteUInt16(|entry.ciphertext| as uint16);
      totalWritten := totalWritten + len;
      len :- wr.WriteSeq(entry.ciphertext);
      totalWritten := totalWritten + len;
      j := j + 1;
    }
    return Success(totalWritten);
  }
}

module CMMDefs {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Materials = Materials

  import AlgorithmSuite = AlgorithmSuite

  import Signature = Signature

  import MessageHeader = MessageHeader
  trait {:termination false} CMM {
    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      decreases Repr + {this}

    method GetEncryptionMaterials(encCtx: Materials.EncryptionContext, algSuiteID: Option<AlgorithmSuite.ID>, plaintextLen: Option<nat>)
        returns (res: Result<Materials.ValidEncryptionMaterials>)
      requires Valid()
      requires ValidAAD(encCtx) && Materials.GetKeysFromEncryptionContext(encCtx) !! Materials.ReservedKeyValues
      ensures Valid()
      ensures res.Success? ==> res.value.dataKeyMaterials.algorithmSuiteID.ValidPlaintextDataKey(res.value.dataKeyMaterials.plaintextDataKey)
      ensures res.Success? ==> |res.value.dataKeyMaterials.encryptedDataKeys| > 0
      ensures res.Success? ==> ValidAAD(res.value.encryptionContext)
      ensures res.Success? ==> match res.value.dataKeyMaterials.algorithmSuiteID.SignatureType() case None => true case Some(sigType) => res.value.signingKey.Some? && Signature.ECDSA.WfSK(sigType, res.value.signingKey.get)
      decreases encCtx, algSuiteID, plaintextLen

    predicate ValidAAD(encryptionContext: Materials.EncryptionContext)
      decreases encryptionContext
    {
      MessageHeader.ValidAAD(encryptionContext)
    }

    method DecryptMaterials(algSuiteID: AlgorithmSuite.ID, edks: seq<Materials.EncryptedDataKey>, encCtx: Materials.EncryptionContext)
        returns (res: Result<Materials.ValidDecryptionMaterials>)
      requires |edks| > 0
      requires Valid()
      ensures Valid()
      ensures res.Success? ==> res.value.algorithmSuiteID.ValidPlaintextDataKey(res.value.plaintextDataKey)
      ensures res.Success? && res.value.algorithmSuiteID.SignatureType().Some? ==> res.value.verificationKey.Some?
      decreases algSuiteID, edks, encCtx
  }
}

module MessageHeader {

  import AlgorithmSuite = AlgorithmSuite

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import Materials = Materials

  import UTF8 = UTF8
  datatype Header = Header(body: HeaderBody, auth: HeaderAuthentication) {
    predicate Valid()
      decreases this
    {
      body.Valid() &&
      |auth.iv| == body.algorithmSuiteID.IVLength() &&
      |auth.authenticationTag| == body.algorithmSuiteID.TagLength()
    }
  }

  type Version = x: uint8
    | x == VERSION_1
    witness VERSION_1

  type Type = x: uint8
    | x == TYPE_CUSTOMER_AED
    witness TYPE_CUSTOMER_AED

  type MessageID = x: seq<uint8>
    | |x| == MESSAGE_ID_LEN
    witness [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

  datatype ContentType = NonFramed | Framed

  datatype EncryptedDataKeys = EncryptedDataKeys(entries: seq<Materials.EncryptedDataKey>) {
    predicate Valid()
      decreases this
    {
      0 < |entries| < UINT16_LIMIT &&
      forall i: int :: 
        0 <= i < |entries| ==>
          entries[i].Valid()
    }
  }

  datatype HeaderBody = HeaderBody(version: Version, typ: Type, algorithmSuiteID: AlgorithmSuite.ID, messageID: MessageID, aad: Materials.EncryptionContext, encryptedDataKeys: EncryptedDataKeys, contentType: ContentType, ivLength: uint8, frameLength: uint32) {
    predicate Valid()
      decreases this
    {
      ValidAAD(aad) &&
      encryptedDataKeys.Valid() &&
      algorithmSuiteID.IVLength() == ivLength as nat &&
      ValidFrameLength(frameLength, contentType)
    }
  }

  datatype HeaderAuthentication = HeaderAuthentication(iv: seq<uint8>, authenticationTag: seq<uint8>)

  const VERSION_1: uint8 := 1
  const TYPE_CUSTOMER_AED: uint8 := 128
  const MESSAGE_ID_LEN := 16
  const Reserved: seq<uint8> := [0, 0, 0, 0]

  function method ContentTypeToUInt8(contentType: ContentType): uint8
    decreases contentType
  {
    match contentType
    case NonFramed =>
      1
    case Framed =>
      2
  }

  function method UInt8ToContentType(x: uint8): Option<ContentType>
    decreases x
  {
    if x == 1 then
      Some(NonFramed)
    else if x == 2 then
      Some(Framed)
    else
      None
  }

  lemma ContentTypeConversionsCorrect(contentType: ContentType, x: uint8)
    ensures UInt8ToContentType(ContentTypeToUInt8(contentType)) == Some(contentType)
    ensures var opt: Option<ContentType> := UInt8ToContentType(x); opt == None || ContentTypeToUInt8(opt.get) == x
    decreases contentType, x
  {
  }

  predicate ValidKVPair(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes))
    decreases kvPair
  {
    |kvPair.0| < UINT16_LIMIT &&
    |kvPair.1| < UINT16_LIMIT &&
    UTF8.ValidUTF8Seq(kvPair.0) &&
    UTF8.ValidUTF8Seq(kvPair.1)
  }

  function KVPairsLength(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat): nat
    requires lo <= hi <= |kvPairs|
    decreases kvPairs, lo, hi
  {
    if lo == hi then
      0
    else
      KVPairsLength(kvPairs, lo, hi - 1) + 2 + |kvPairs[hi - 1].0| + 2 + |kvPairs[hi - 1].1|
  }

  lemma /*{:_induction kvPairs, lo, mid, hi}*/ KVPairsLengthSplit(kvPairs: Materials.EncryptionContext, lo: nat, mid: nat, hi: nat)
    requires lo <= mid <= hi <= |kvPairs|
    ensures KVPairsLength(kvPairs, lo, hi) == KVPairsLength(kvPairs, lo, mid) + KVPairsLength(kvPairs, mid, hi)
    decreases kvPairs, lo, mid, hi
  {
  }

  lemma /*{:_induction kvPairs, more}*/ KVPairsLengthPrefix(kvPairs: Materials.EncryptionContext, more: Materials.EncryptionContext)
    ensures KVPairsLength(kvPairs + more, 0, |kvPairs|) == KVPairsLength(kvPairs, 0, |kvPairs|)
    decreases kvPairs, more
  {
  }

  lemma /*{:_induction kvPairs}*/ KVPairsLengthExtend(kvPairs: Materials.EncryptionContext, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
    ensures KVPairsLength(kvPairs + [(key, value)], 0, |kvPairs| + 1) == KVPairsLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
    decreases kvPairs, key, value
  {
  }

  lemma /*{:_induction kvPairs}*/ KVPairsLengthInsert(kvPairs: Materials.EncryptionContext, insertionPoint: nat, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
    requires insertionPoint <= |kvPairs|
    ensures var kvPairs': seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)> := kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..]; KVPairsLength(kvPairs', 0, |kvPairs'|) == KVPairsLength(kvPairs, 0, |kvPairs|) + 4 + |key| + |value|
    decreases |kvPairs|
  {
  }

  function AADLength(kvPairs: Materials.EncryptionContext): nat
    decreases kvPairs
  {
    if |kvPairs| == 0 then
      0
    else
      2 + KVPairsLength(kvPairs, 0, |kvPairs|)
  }

  predicate {:opaque} {:fuel 0, 0} ValidAAD(kvPairs: Materials.EncryptionContext)
    decreases kvPairs
  {
    |kvPairs| < UINT16_LIMIT &&
    (forall i: int :: 
      0 <= i < |kvPairs| ==>
        ValidKVPair(kvPairs[i])) &&
    SortedKVPairs(kvPairs) &&
    AADLength(kvPairs) < UINT16_LIMIT
  }

  lemma {:axiom} AssumeValidAAD(kvPairs: Materials.EncryptionContext)
    ensures ValidAAD(kvPairs)
    decreases kvPairs

  predicate ValidFrameLength(frameLength: uint32, contentType: ContentType)
    decreases frameLength, contentType
  {
    match contentType
    case NonFramed =>
      frameLength == 0
    case Framed =>
      frameLength != 0
  }

  predicate SortedKVPairsUpTo(a: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>, n: nat)
    requires n <= |a|
    decreases a, n
  {
    forall j: int :: 
      0 < j < n ==>
        LexicographicLessOrEqual(a[j - 1].0, a[j].0, UInt8Less)
  }

  predicate SortedKVPairs(a: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>)
    decreases a
  {
    SortedKVPairsUpTo(a, |a|)
  }

  function {:opaque} {:fuel 0, 0} HeaderBodyToSeq(hb: HeaderBody): seq<uint8>
    requires hb.Valid()
    decreases hb
  {
    [hb.version as uint8] + [hb.typ as uint8] + UInt16ToSeq(hb.algorithmSuiteID as uint16) + hb.messageID + AADToSeq(hb.aad) + EDKsToSeq(hb.encryptedDataKeys) + [ContentTypeToUInt8(hb.contentType)] + Reserved + [hb.ivLength] + UInt32ToSeq(hb.frameLength)
  }

  function AADToSeq(kvPairs: Materials.EncryptionContext): seq<uint8>
    requires ValidAAD(kvPairs)
    decreases kvPairs
  {
    reveal ValidAAD();
    UInt16ToSeq(AADLength(kvPairs) as uint16) + var n: int := |kvPairs|; if n == 0 then [] else UInt16ToSeq(n as uint16) + KVPairsToSeq(kvPairs, 0, n)
  }

  function KVPairsToSeq(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat): seq<uint8>
    requires forall i: int :: 0 <= i < |kvPairs| ==> ValidKVPair(kvPairs[i])
    requires lo <= hi <= |kvPairs|
    decreases kvPairs, lo, hi
  {
    if lo == hi then
      []
    else
      KVPairsToSeq(kvPairs, lo, hi - 1) + KVPairToSeq(kvPairs[hi - 1])
  }

  function KVPairToSeq(kvPair: (UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)): seq<uint8>
    requires ValidKVPair(kvPair)
    decreases kvPair
  {
    UInt16ToSeq(|kvPair.0| as uint16) + kvPair.0 + UInt16ToSeq(|kvPair.1| as uint16) + kvPair.1
  }

  function EDKsToSeq(encryptedDataKeys: EncryptedDataKeys): seq<uint8>
    requires encryptedDataKeys.Valid()
    decreases encryptedDataKeys
  {
    var n: int := |encryptedDataKeys.entries|;
    UInt16ToSeq(n as uint16) + EDKEntriesToSeq(encryptedDataKeys.entries, 0, n)
  }

  function EDKEntriesToSeq(entries: seq<Materials.EncryptedDataKey>, lo: nat, hi: nat): seq<uint8>
    requires forall i: int :: 0 <= i < |entries| ==> entries[i].Valid()
    requires lo <= hi <= |entries|
    decreases entries, lo, hi
  {
    if lo == hi then
      []
    else
      EDKEntriesToSeq(entries, lo, hi - 1) + EDKEntryToSeq(entries[hi - 1])
  }

  function EDKEntryToSeq(edk: Materials.EncryptedDataKey): seq<uint8>
    requires edk.Valid()
    decreases edk
  {
    UInt16ToSeq(|edk.providerID| as uint16) + edk.providerID + UInt16ToSeq(|edk.providerInfo| as uint16) + edk.providerInfo + UInt16ToSeq(|edk.ciphertext| as uint16) + edk.ciphertext
  }

  lemma ADDLengthCorrect(kvPairs: Materials.EncryptionContext)
    requires ValidAAD(kvPairs)
    ensures |AADToSeq(kvPairs)| == 2 + AADLength(kvPairs)
    decreases kvPairs
  {
  }

  lemma /*{:_induction kvPairs, lo, hi}*/ KVPairsLengthCorrect(kvPairs: Materials.EncryptionContext, lo: nat, hi: nat)
    requires forall i: int :: 0 <= i < |kvPairs| ==> ValidKVPair(kvPairs[i])
    requires lo <= hi <= |kvPairs|
    ensures |KVPairsToSeq(kvPairs, lo, hi)| == KVPairsLength(kvPairs, lo, hi)
    decreases kvPairs, lo, hi
  {
  }
}

module Deserialize {

  export 
    provides DeserializeHeader, Streams, StandardLibrary, UInt, AlgorithmSuite, Msg, InsertNewEntry, UTF8


  import Msg = MessageHeader

  import AlgorithmSuite = AlgorithmSuite

  import Streams = Streams

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import UTF8 = UTF8

  import Materials = Materials
  method DeserializeHeader(rd: Streams.StringReader) returns (res: Result<Msg.Header>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match res case Success(header) => header.Valid() case Failure(_) => true
    decreases rd
  {
    var hb :- DeserializeHeaderBody(rd);
    var auth :- DeserializeHeaderAuthentication(rd, hb.algorithmSuiteID);
    return Success(Msg.Header(hb, auth));
  }

  method DeserializeHeaderBody(rd: Streams.StringReader) returns (ret: Result<Msg.HeaderBody>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret case Success(hb) => hb.Valid() case Failure(_) => true
    decreases rd
  {
    var version :- DeserializeVersion(rd);
    var typ :- DeserializeType(rd);
    var algorithmSuiteID :- DeserializeAlgorithmSuiteID(rd);
    var messageID :- DeserializeMsgID(rd);
    var aad :- DeserializeAAD(rd);
    var encryptedDataKeys :- DeserializeEncryptedDataKeys(rd);
    var contentType :- DeserializeContentType(rd);
    var _ :- DeserializeReserved(rd);
    var ivLength :- rd.ReadByte();
    var frameLength :- rd.ReadUInt32();
    if ivLength as nat != algorithmSuiteID.IVLength() {
      return Failure(""Deserialization Error: Incorrect IV length."");
    }
    if contentType.NonFramed? && frameLength != 0 {
      return Failure(""Deserialization Error: Frame length must be 0 when content type is non-framed."");
    } else if contentType.Framed? && frameLength == 0 {
      return Failure(""Deserialization Error: Frame length must be non-0 when content type is framed."");
    }
    var hb := Msg.HeaderBody(version, typ, algorithmSuiteID, messageID, aad, encryptedDataKeys, contentType, ivLength, frameLength);
    return Success(hb);
  }

  method DeserializeHeaderAuthentication(rd: Streams.StringReader, algorithmSuiteID: AlgorithmSuite.ID) returns (ret: Result<Msg.HeaderAuthentication>)
    requires rd.Valid()
    requires algorithmSuiteID in AlgorithmSuite.Suite.Keys
    modifies rd
    ensures rd.Valid()
    ensures match ret case Success(ha) => |ha.iv| == algorithmSuiteID.IVLength() && |ha.authenticationTag| == algorithmSuiteID.TagLength() case Failure(_) => true
    decreases rd, algorithmSuiteID
  {
    var iv :- rd.ReadExact(algorithmSuiteID.IVLength());
    var authenticationTag :- rd.ReadExact(algorithmSuiteID.TagLength());
    return Success(Msg.HeaderAuthentication(iv, authenticationTag));
  }

  method DeserializeVersion(rd: Streams.StringReader) returns (ret: Result<Msg.Version>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    decreases rd
  {
    var version :- rd.ReadByte();
    if version == Msg.VERSION_1 {
      return Success(version);
    } else {
      return Failure(""Deserialization Error: Version not supported."");
    }
  }

  method DeserializeType(rd: Streams.StringReader) returns (ret: Result<Msg.Type>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    decreases rd
  {
    var typ :- rd.ReadByte();
    if typ == Msg.TYPE_CUSTOMER_AED {
      return Success(typ);
    } else {
      return Failure(""Deserialization Error: Type not supported."");
    }
  }

  method DeserializeAlgorithmSuiteID(rd: Streams.StringReader) returns (ret: Result<AlgorithmSuite.ID>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    decreases rd
  {
    var algorithmSuiteID :- rd.ReadUInt16();
    if algorithmSuiteID in AlgorithmSuite.VALID_IDS {
      return Success(algorithmSuiteID as AlgorithmSuite.ID);
    } else {
      return Failure(""Deserialization Error: Algorithm suite not supported."");
    }
  }

  method DeserializeMsgID(rd: Streams.StringReader) returns (ret: Result<Msg.MessageID>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    decreases rd
  {
    var msgID: seq<uint8> :- rd.ReadExact(Msg.MESSAGE_ID_LEN);
    return Success(msgID);
  }

  method DeserializeUTF8(rd: Streams.StringReader, n: nat) returns (ret: Result<seq<uint8>>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret case Success(bytes) => |bytes| == n && UTF8.ValidUTF8Seq(bytes) case Failure(_) => true
    decreases rd, n
  {
    var bytes :- rd.ReadExact(n);
    if UTF8.ValidUTF8Seq(bytes) {
      return Success(bytes);
    } else {
      return Failure(""Deserialization Error: Not a valid UTF8 string."");
    }
  }

  method DeserializeAAD(rd: Streams.StringReader) returns (ret: Result<Materials.EncryptionContext>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret case Success(aad) => Msg.ValidAAD(aad) case Failure(_) => true
    decreases rd
  {
    reveal Msg.ValidAAD();
    var aadLength :- rd.ReadUInt16();
    if aadLength == 0 {
      return Success([]);
    } else if aadLength < 2 {
      return Failure(""Deserialization Error: The number of bytes in encryption context exceeds the given length."");
    }
    var totalBytesRead := 0;
    var kvPairsCount :- rd.ReadUInt16();
    totalBytesRead := totalBytesRead + 2;
    if kvPairsCount == 0 {
      return Failure(""Deserialization Error: Key value pairs count is 0."");
    }
    var kvPairs: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)> := [];
    var i := 0;
    while i < kvPairsCount
      invariant rd.Valid()
      invariant |kvPairs| == i as int
      invariant i <= kvPairsCount
      invariant totalBytesRead == 2 + Msg.KVPairsLength(kvPairs, 0, i as nat) <= aadLength as nat
      invariant Msg.ValidAAD(kvPairs)
      decreases kvPairsCount as int - i as int
    {
      var keyLength :- rd.ReadUInt16();
      totalBytesRead := totalBytesRead + 2;
      var key :- DeserializeUTF8(rd, keyLength as nat);
      totalBytesRead := totalBytesRead + |key|;
      var valueLength :- rd.ReadUInt16();
      totalBytesRead := totalBytesRead + 2;
      if aadLength as nat < totalBytesRead + valueLength as nat {
        return Failure(""Deserialization Error: The number of bytes in encryption context exceeds the given length."");
      }
      var value :- DeserializeUTF8(rd, valueLength as nat);
      totalBytesRead := totalBytesRead + |value|;
      var opt, insertionPoint := InsertNewEntry(kvPairs, key, value);
      match opt {
        case Some(kvPairs_) =>
          Msg.KVPairsLengthInsert(kvPairs, insertionPoint, key, value);
          kvPairs := kvPairs_;
        case None =>
          return Failure(""Deserialization Error: Duplicate key."");
      }
      i := i + 1;
    }
    if aadLength as nat != totalBytesRead {
      return Failure(""Deserialization Error: Bytes actually read differs from bytes supposed to be read."");
    }
    return Success(kvPairs);
  }

  method InsertNewEntry(kvPairs: seq<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes)>, key: UTF8.ValidUTF8Bytes, value: UTF8.ValidUTF8Bytes)
      returns (res: Option<seq<(seq<uint8>, seq<uint8>)>>, ghost insertionPoint: nat)
    requires Msg.SortedKVPairs(kvPairs)
    ensures match res case None => (exists i :: 0 <= i < |kvPairs| && kvPairs[i].0 == key) case Some(kvPairs') => insertionPoint <= |kvPairs| && kvPairs' == kvPairs[..insertionPoint] + [(key, value)] + kvPairs[insertionPoint..] && Msg.SortedKVPairs(kvPairs')
    decreases kvPairs, key, value
  {
    var n := |kvPairs|;
    while 0 < n && LexicographicLessOrEqual(key, kvPairs[n - 1].0, UInt8Less)
      invariant 0 <= n <= |kvPairs|
      invariant forall i: int :: n <= i < |kvPairs| ==> LexicographicLessOrEqual(key, kvPairs[i].0, UInt8Less)
      decreases n - 0
    {
      n := n - 1;
    }
    if 0 < n && kvPairs[n - 1].0 == key {
      return None, n;
    } else {
      var kvPairs' := kvPairs[..n] + [(key, value)] + kvPairs[n..];
      if 0 < n {
        LexPreservesTrichotomy(kvPairs'[n - 1].0, kvPairs'[n].0, UInt8Less);
      }
      return Some(kvPairs'), n;
    }
  }

  method DeserializeEncryptedDataKeys(rd: Streams.StringReader) returns (ret: Result<Msg.EncryptedDataKeys>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    ensures match ret case Success(edks) => edks.Valid() case Failure(_) => true
    decreases rd
  {
    var edkCount :- rd.ReadUInt16();
    if edkCount == 0 {
      return Failure(""Deserialization Error: Encrypted data key count is 0."");
    }
    var edkEntries: seq<Materials.EncryptedDataKey> := [];
    var i := 0;
    while i < edkCount
      invariant rd.Valid()
      invariant i <= edkCount
      invariant |edkEntries| == i as int
      invariant forall i: int :: 0 <= i < |edkEntries| ==> edkEntries[i].Valid()
      decreases edkCount as int - i as int
    {
      var keyProviderIDLength :- rd.ReadUInt16();
      var str :- DeserializeUTF8(rd, keyProviderIDLength as nat);
      var keyProviderID := str;
      var keyProviderInfoLength :- rd.ReadUInt16();
      var keyProviderInfo :- rd.ReadExact(keyProviderInfoLength as nat);
      var edkLength :- rd.ReadUInt16();
      var edk :- rd.ReadExact(edkLength as nat);
      edkEntries := edkEntries + [Materials.EncryptedDataKey(keyProviderID, keyProviderInfo, edk)];
      i := i + 1;
    }
    var edks := Msg.EncryptedDataKeys(edkEntries);
    return Success(edks);
  }

  method DeserializeContentType(rd: Streams.StringReader) returns (ret: Result<Msg.ContentType>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    decreases rd
  {
    var byte :- rd.ReadByte();
    match Msg.UInt8ToContentType(byte)
    case None =>
      return Failure(""Deserialization Error: Content type not supported."");
    case Some(contentType) =>
      return Success(contentType);
  }

  method DeserializeReserved(rd: Streams.StringReader) returns (ret: Result<seq<uint8>>)
    requires rd.Valid()
    modifies rd
    ensures rd.Valid()
    decreases rd
  {
    var reserved :- rd.ReadExact(4);
    if reserved == Msg.Reserved {
      return Success(reserved);
    } else {
      return Failure(""Deserialization Error: Reserved fields must be 0."");
    }
  }
}

module MessageBody {

  export 
    provides EncryptMessageBody, DecryptFramedMessageBody, StandardLibrary, UInt, Msg, AlgorithmSuite, Materials, Streams


  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import AlgorithmSuite = AlgorithmSuite

  import Msg = MessageHeader

  import AESEncryption = AESEncryption

  import Materials = Materials

  import Streams = Streams

  import EncryptionSuites = EncryptionSuites

  import UTF8 = UTF8
  const BODY_AAD_CONTENT_REGULAR_FRAME := UTF8.Encode(""AWSKMSEncryptionClient Frame"").value
  const BODY_AAD_CONTENT_FINAL_FRAME := UTF8.Encode(""AWSKMSEncryptionClient Final Frame"").value
  const START_SEQUENCE_NUMBER: uint32 := 1
  const ENDFRAME_SEQUENCE_NUMBER: uint32 := 4294967295

  method EncryptMessageBody(plaintext: seq<uint8>, frameLength: int, messageID: Msg.MessageID, key: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID)
      returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    decreases plaintext, frameLength, messageID, key, algorithmSuiteID
  {
    var body := [];
    var n, sequenceNumber := 0, START_SEQUENCE_NUMBER;
    while n + frameLength < |plaintext|
      invariant 0 <= n <= |plaintext|
      invariant START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
      decreases |plaintext| - (n + frameLength)
    {
      if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
        return Failure(""too many frames"");
      }
      var plaintextFrame := plaintext[n .. n + frameLength];
      var regularFrame :- EncryptRegularFrame(algorithmSuiteID, key, frameLength, messageID, plaintextFrame, sequenceNumber);
      body := body + regularFrame;
      n, sequenceNumber := n + frameLength, sequenceNumber + 1;
    }
    var finalFrame :- EncryptFinalFrame(algorithmSuiteID, key, frameLength, messageID, plaintext[n..], sequenceNumber);
    body := body + finalFrame;
    return Success(body);
  }

  method EncryptRegularFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, ghost frameLength: int, messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| == frameLength && sequenceNumber != ENDFRAME_SEQUENCE_NUMBER
    requires 4 <= algorithmSuiteID.IVLength()
    decreases algorithmSuiteID, key, frameLength, messageID, plaintext, sequenceNumber
  {
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    var unauthenticatedFrame := seqNumSeq;
    var iv := seq(algorithmSuiteID.IVLength() - 4, (_: int) => 0) + UInt32ToSeq(sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);
    unauthenticatedFrame := unauthenticatedFrame + iv;
    var aad := BodyAAD(messageID, false, sequenceNumber, |plaintext| as uint64);
    var encryptionOutput :- AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    return Success(unauthenticatedFrame);
  }

  method EncryptFinalFrame(algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID, plaintext: seq<uint8>, sequenceNumber: uint32)
      returns (res: Result<seq<uint8>>)
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength && START_SEQUENCE_NUMBER <= sequenceNumber <= ENDFRAME_SEQUENCE_NUMBER
    requires |plaintext| < UINT32_LIMIT
    requires |plaintext| <= frameLength
    requires 4 <= algorithmSuiteID.IVLength()
    decreases algorithmSuiteID, key, frameLength, messageID, plaintext, sequenceNumber
  {
    var unauthenticatedFrame := UInt32ToSeq(ENDFRAME_SEQUENCE_NUMBER);
    var seqNumSeq := UInt32ToSeq(sequenceNumber);
    unauthenticatedFrame := unauthenticatedFrame + seqNumSeq;
    var iv := seq(algorithmSuiteID.IVLength() - 4, (_: int) => 0) + UInt32ToSeq(sequenceNumber);
    SeqWithUInt32Suffix(iv, sequenceNumber as nat);
    unauthenticatedFrame := unauthenticatedFrame + iv;
    unauthenticatedFrame := unauthenticatedFrame + UInt32ToSeq(|plaintext| as uint32);
    var aad := BodyAAD(messageID, true, sequenceNumber, |plaintext| as uint64);
    var encryptionOutput :- AESEncryption.AESEncrypt(algorithmSuiteID.EncryptionSuite(), iv, key, plaintext, aad);
    unauthenticatedFrame := unauthenticatedFrame + encryptionOutput.cipherText + encryptionOutput.authTag;
    return Success(unauthenticatedFrame);
  }

  method DecryptFramedMessageBody(rd: Streams.StringReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID)
      returns (res: Result<seq<uint8>>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd
    ensures rd.Valid()
    decreases rd, algorithmSuiteID, key, frameLength, messageID
  {
    var plaintext := [];
    var n := 1;
    while true
      invariant rd.Valid()
      decreases ENDFRAME_SEQUENCE_NUMBER - n
    {
      var pair :- DecryptFrame(rd, algorithmSuiteID, key, frameLength, messageID, n);
      var (framePlaintext, final) := pair;

      plaintext := plaintext + framePlaintext;
      if final {
        break;
      }
      n := n + 1;
    }
    return Success(plaintext);
  }

  method DecryptFrame(rd: Streams.StringReader, algorithmSuiteID: AlgorithmSuite.ID, key: seq<uint8>, frameLength: int, messageID: Msg.MessageID, expectedSequenceNumber: uint32)
      returns (res: Result<(seq<uint8>, bool)>)
    requires rd.Valid()
    requires |key| == algorithmSuiteID.KeyLength()
    requires 0 < frameLength < UINT32_LIMIT
    modifies rd
    ensures rd.Valid()
    ensures match res case Success((plaintext, final)) => expectedSequenceNumber == ENDFRAME_SEQUENCE_NUMBER ==> final case Failure(_) => true
    decreases rd, algorithmSuiteID, key, frameLength, messageID, expectedSequenceNumber
  {
    var final := false;
    var sequenceNumber :- rd.ReadUInt32();
    if sequenceNumber == ENDFRAME_SEQUENCE_NUMBER {
      final := true;
      sequenceNumber :- rd.ReadUInt32();
    }
    if sequenceNumber != expectedSequenceNumber {
      return Failure(""unexpected frame sequence number"");
    }
    var iv :- rd.ReadExact(algorithmSuiteID.IVLength());
    var len := frameLength as uint32;
    if final {
      len :- rd.ReadUInt32();
    }
    var aad := BodyAAD(messageID, final, sequenceNumber, len as uint64);
    var ciphertext :- rd.ReadExact(len as nat);
    var authTag :- rd.ReadExact(algorithmSuiteID.TagLength());
    var plaintext :- Decrypt(ciphertext, authTag, algorithmSuiteID, iv, key, aad);
    return Success((plaintext, final));
  }

  method BodyAAD(messageID: seq<uint8>, final: bool, sequenceNumber: uint32, length: uint64)
      returns (aad: seq<uint8>)
    decreases messageID, final, sequenceNumber, length
  {
    var contentAAD := if final then BODY_AAD_CONTENT_FINAL_FRAME else BODY_AAD_CONTENT_REGULAR_FRAME;
    aad := messageID + contentAAD + UInt32ToSeq(sequenceNumber) + UInt64ToSeq(length);
  }

  method Decrypt(ciphertext: seq<uint8>, authTag: seq<uint8>, algorithmSuiteID: AlgorithmSuite.ID, iv: seq<uint8>, key: seq<uint8>, aad: seq<uint8>)
      returns (res: Result<seq<uint8>>)
    requires |iv| == algorithmSuiteID.IVLength()
    requires |key| == algorithmSuiteID.KeyLength()
    requires |authTag| == algorithmSuiteID.TagLength()
    decreases ciphertext, authTag, algorithmSuiteID, iv, key, aad
  {
    var encAlg := algorithmSuiteID.EncryptionSuite();
    res := AESEncryption.AESDecrypt(encAlg, key, ciphertext, authTag, iv, aad);
  }
}

module {:extern ""Digests""} Digests {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  datatype {:extern ""HMAC_ALGORITHM""} HMAC_ALGORITHM = HmacSHA256 | HmacSHA384 | HmacNOSHA

  function {:axiom} HashLength(algorithm: HMAC_ALGORITHM): nat
    ensures algorithm == HmacSHA256 ==> HashLength(algorithm) == 32
    ensures algorithm == HmacSHA384 ==> HashLength(algorithm) == 48
    decreases algorithm

  function {:axiom} Hash(algorithm: HMAC_ALGORITHM, key: seq<uint8>, message: seq<uint8>): seq<uint8>
    ensures |Hash(algorithm, key, message)| == HashLength(algorithm)
    decreases algorithm, key, message
}

module HKDF {

  import Arrays = Arrays

  import opened BouncyCastleCryptoMac = BouncyCastleCryptoMac

  import opened Digests = Digests

  import opened HKDFSpec = HKDFSpec

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  method extract(which_sha: HMAC_ALGORITHM, hmac: HMac, salt: array<uint8>, ikm: array<uint8>)
      returns (prk: array<uint8>)
    requires hmac.algorithm == which_sha && salt.Length != 0
    modifies hmac
    ensures prk[..] == Hash(which_sha, salt[..], ikm[..])
    decreases which_sha, hmac, salt, ikm
  {
    var params: CipherParameters := KeyParameter(salt);
    hmac.init(params);
    assert hmac.InputSoFar + ikm[..] == ikm[..];
    hmac.updateAll(ikm);
    prk := new uint8[hmac.getMacSize()];
    var _ := hmac.doFinal(prk, 0);
    return prk;
  }

  method expand(which_sha: HMAC_ALGORITHM, hmac: HMac, prk: array<uint8>, info: array<uint8>, n: int)
      returns (a: array<uint8>)
    requires hmac.algorithm == which_sha && 1 <= n <= 255
    requires 0 != prk.Length && HashLength(which_sha) <= prk.Length
    modifies hmac
    ensures fresh(a)
    ensures a[..] == T(which_sha, prk[..], info[..], n)
    ensures a.Length == n * hmac.getMacSize()
    decreases which_sha, hmac, prk, info, n
  {
    var params: CipherParameters := KeyParameter(prk);
    hmac.init(params);
    ghost var gKey := hmac.initialized.get;
    ghost var s: seq<uint8> := [];
    a := new uint8[n * hmac.getMacSize()];
    var TiArr: array<uint8> := new uint8[hmac.getMacSize()];
    hmac.updateAll(info);
    hmac.updateSingle(1 as uint8);
    var _ := hmac.doFinal(TiArr, 0);
    Arrays.Array.copyTo(TiArr, a, 0);
    s := s + TiArr[..];
    var i := 1;
    assert hmac.getMacSize() + (n - 1) * TiArr.Length == a.Length;
    while i < n
      invariant 1 <= i <= n
      invariant TiArr.Length == HashLength(which_sha)
      invariant TiArr[..] == Ti(which_sha, prk[..], info[..], i)[..]
      invariant HashLength(which_sha) <= prk.Length
      invariant s == T(which_sha, prk[..], info[..], i)
      invariant s == a[..i * hmac.getMacSize()]
      invariant hmac.initialized.Some? && hmac.initialized.get == gKey
      invariant hmac.InputSoFar == []
      decreases n - i
    {
      hmac.updateAll(TiArr);
      hmac.updateAll(info);
      hmac.updateSingle((i + 1) as uint8);
      assert i + 1 <= 255;
      assert hmac.InputSoFar[..] == TiArr[..] + info[..] + [(i + 1) as uint8];
      var _ := hmac.doFinal(TiArr, 0);
      Arrays.Array.copyTo(TiArr, a, i * hmac.getMacSize());
      s := s + TiArr[..];
      i := i + 1;
    }
  }

  method hkdf(which_sha: HMAC_ALGORITHM, salt: Option<array<uint8>>, ikm: array<uint8>, info: array<uint8>, L: int)
      returns (okm: array<uint8>)
    requires which_sha == HmacSHA256 || which_sha == HmacSHA384
    requires 0 <= L <= 255 * HashLength(which_sha)
    requires salt.None? || salt.get.Length != 0
    ensures fresh(okm)
    ensures okm.Length == L
    ensures var prk: seq<uint8> := Hash(which_sha, if salt.None? then Fill(0, HashLength(which_sha)) else salt.get[..], ikm[..]); okm[..L] == TMaxLength(which_sha, prk, info[..])[..L]
    decreases which_sha, salt, ikm, info, L
  {
    if L == 0 {
      return new uint8[0];
    }
    var hmac := new HMac(which_sha);
    var saltNonEmpty: array<uint8>;
    match salt {
      case None =>
        saltNonEmpty := new uint8[hmac.getMacSize()] (_ => 0);
      case Some(s) =>
        saltNonEmpty := s;
    }
    assert saltNonEmpty[..] == if salt.None? then Fill(0, hmac.getMacSize()) else salt.get[..];
    var n := 1 + (L - 1) / hmac.getMacSize();
    assert n * hmac.getMacSize() >= L;
    var prk := extract(which_sha, hmac, saltNonEmpty, ikm);
    okm := expand(which_sha, hmac, prk, info, n);
    if okm.Length > L {
      okm := Arrays.Array.copy(okm, L);
    }
    calc {
      okm[..L];
    ==
      T(which_sha, prk[..], info[..], n)[..L];
    ==
      {
        TPrefix(which_sha, prk[..], info[..], n, 255);
      }
      TMaxLength(which_sha, prk[..], info[..])[..L];
    }
  }
}

module {:extern ""Signature""} Signature {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  datatype {:extern ""ECDSAParams""} ECDSAParams = ECDSA_P384 | ECDSA_P256 {
    function method SignatureLength(): uint16
      decreases this
    {
      match this
      case ECDSA_P256 =>
        71
      case ECDSA_P384 =>
        103
    }
  }

  type Sig = (seq<uint8>, seq<uint8>)

  class {:extern ""ECDSA""} ECDSA {
    static predicate {:axiom} WfSig(s: ECDSAParams, sig: Sig)
      decreases s, sig

    static predicate {:axiom} WfSK(s: ECDSAParams, sk: seq<uint8>)
      decreases s, sk

    static predicate {:axiom} WfVK(s: ECDSAParams, vk: seq<uint8>)
      decreases s, vk

    static predicate {:axiom} IsSignKeypair(s: ECDSAParams, sk: seq<uint8>, vk: seq<uint8>)
      decreases s, sk, vk

    static method {:extern ""KeyGen""} KeyGen(s: ECDSAParams) returns (res: Option<(seq<uint8>, seq<uint8>)>)
      ensures res.Some? ==> WfSK(s, res.get.1)
      ensures res.Some? ==> WfVK(s, res.get.0)
      ensures res.Some? ==> IsSignKeypair(s, res.get.1, res.get.0)
      decreases s
  }

  method {:extern ""Signature.ECDSA"", ""Sign""} Sign(s: ECDSAParams, key: seq<uint8>, digest: seq<uint8>)
      returns (sig: Option<seq<uint8>>)
    requires ECDSA.WfSK(s, key)
    ensures sig.Some? ==> |sig.get| == s.SignatureLength() as int
    decreases s, key, digest

  function method {:extern ""Signature.ECDSA"", ""Verify""} Verify(s: ECDSAParams, key: seq<uint8>, msg: seq<uint8>, sig: seq<uint8>): bool
    decreases s, key, msg, sig

  method {:extern ""Signature.ECDSA"", ""Digest""} Digest(s: ECDSAParams, msg: seq<uint8>) returns (digest: seq<uint8>)
    decreases s, msg
}

module {:extern ""Arrays""} Arrays {
  class {:extern ""Array""} Array {
    static method {:extern ""copy""} copy<T>(source: array<T>, length: nat) returns (dest: array<T>)
      requires length <= source.Length
      ensures dest.Length == length
      ensures fresh(dest) && forall i: int :: 0 <= i < length ==> dest[i] == source[i]
      decreases source, length

    static method {:extern ""copyTo""} copyTo<T>(source: array<T>, dest: array<T>, offset: nat)
      requires source != dest
      requires offset + source.Length <= dest.Length
      modifies dest
      ensures dest.Length == old(dest.Length)
      ensures dest[..] == old(dest[..offset]) + source[..] + old(dest[offset + source.Length..])
      ensures source[..] == old(source[..])
      decreases source, dest, offset
  }
}

module {:extern ""BouncyCastleCryptoMac""} BouncyCastleCryptoMac {

  import opened Digests = Digests

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt
  datatype {:extern ""CipherParameters""} CipherParameters = KeyParameter(key: array<uint8>)

  trait {:extern ""Mac""} Mac {
    const {:extern ""algorithm""} algorithm: HMAC_ALGORITHM

    function method {:extern ""getAlgorithmName""} getAlgorithmName(): string
      ensures this.algorithm == HmacSHA256 ==> getAlgorithmName() == ""SHA256""
      ensures this.algorithm == HmacSHA384 ==> getAlgorithmName() == ""SHA384""

    function method {:extern ""getMacSize""} getMacSize(): nat
      reads this
      ensures getMacSize() == HashLength(algorithm)
      decreases {this}

    ghost var initialized: Option<seq<uint8>>

    predicate {:axiom} validKey(key: seq<uint8>)
      decreases key

    method {:extern ""init""} init(params: CipherParameters)
      requires params.KeyParameter?
      modifies this
      ensures var key: array?<uint8> := match params case KeyParameter(key) => key; match initialized { case Some(k) => validKey(k) && key[..] == k case None => false }
      ensures InputSoFar == []
      decreases params

    ghost var InputSoFar: seq<uint8>

    method {:extern ""reset""} reset()
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == []

    method {:extern ""updateSingle""} updateSingle(input: uint8)
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + [input]
      decreases input

    method {:extern ""update""} update(input: array<uint8>, inOff: nat, len: nat)
      requires initialized.Some?
      requires inOff + len <= input.Length
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[inOff .. inOff + len]
      decreases input, inOff, len

    method {:extern ""doFinal""} doFinal(output: array<uint8>, outOff: nat) returns (retVal: int)
      requires initialized.Some?
      requires outOff + getMacSize() <= output.Length
      requires |Hash(algorithm, initialized.get, InputSoFar)| == getMacSize()
      modifies `InputSoFar, output
      ensures output[..] == old(output[..outOff]) + old(Hash(algorithm, initialized.get, InputSoFar)) + old(output[outOff + getMacSize()..])
      ensures output.Length == old(output.Length)
      ensures InputSoFar == []
      decreases output, outOff
  }

  class {:extern ""HMac""} HMac extends Mac {
    constructor {:extern} (algorithm: HMAC_ALGORITHM)
      ensures this.algorithm == algorithm
      decreases algorithm

    function method {:extern ""getAlgorithmName""} getAlgorithmName(): string
      ensures this.algorithm == HmacSHA256 ==> getAlgorithmName() == ""SHA256""
      ensures this.algorithm == HmacSHA384 ==> getAlgorithmName() == ""SHA384""

    function method {:extern ""getMacSize""} getMacSize(): nat
      reads this
      ensures getMacSize() == HashLength(algorithm)
      decreases {this}

    predicate {:axiom} validKey(key: seq<uint8>)
      decreases key

    method {:extern ""init""} init(params: CipherParameters)
      requires params.KeyParameter?
      modifies this
      ensures var key: array?<uint8> := match params case KeyParameter(key) => key; match initialized { case Some(k) => validKey(k) && key[..] == k case None => false }
      ensures InputSoFar == []
      decreases params

    method {:extern ""reset""} reset()
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == []

    method {:extern ""updateSingle""} updateSingle(input: uint8)
      requires initialized.Some?
      modifies this
      ensures unchanged(`initialized)
      ensures InputSoFar == old(InputSoFar) + [input]
      decreases input

    method {:extern ""update""} update(input: array<uint8>, inOff: nat, len: nat)
      requires initialized.Some?
      requires inOff + len <= input.Length
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[inOff .. inOff + len]
      decreases input, inOff, len

    method {:extern ""doFinal""} doFinal(output: array<uint8>, outOff: nat) returns (retVal: int)
      requires initialized.Some?
      requires outOff + getMacSize() <= output.Length
      requires |Hash(algorithm, initialized.get, InputSoFar)| == getMacSize()
      modifies `InputSoFar, output
      ensures output[..] == old(output[..outOff]) + old(Hash(algorithm, initialized.get, InputSoFar)) + old(output[outOff + getMacSize()..])
      ensures output.Length == old(output.Length)
      ensures InputSoFar == []
      decreases output, outOff

    function method {:extern ""getUnderlyingDigest""} getUnderlyingDigest(): HMAC_ALGORITHM
      ensures getUnderlyingDigest() == algorithm

    method updateAll(input: array<uint8>)
      requires initialized.Some?
      modifies `InputSoFar
      ensures InputSoFar == old(InputSoFar) + input[..]
      decreases input
    {
      update(input, 0, input.Length);
    }
  }
}

module HKDFSpec {

  import opened StandardLibrary = StandardLibrary

  import opened UInt = StandardLibrary.UInt

  import opened Digests = Digests
  function Ti(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, i: nat): seq<uint8>
    requires 0 <= i < 256
    requires HashLength(algorithm) <= |key|
    decreases i, 1
  {
    if i == 0 then
      []
    else
      Hash(algorithm, key, PreTi(algorithm, key, info, i))
  }

  function PreTi(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, i: nat): seq<uint8>
    requires 1 <= i < 256
    requires HashLength(algorithm) <= |key|
    decreases i, 0
  {
    Ti(algorithm, key, info, i - 1) + info + [i as uint8]
  }

  function T(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, n: nat): seq<uint8>
    requires 0 <= n < 256
    requires HashLength(algorithm) <= |key|
    decreases n
  {
    if n == 0 then
      []
    else
      T(algorithm, key, info, n - 1) + Ti(algorithm, key, info, n)
  }

  lemma /*{:_induction algorithm, key, info, n}*/ TLength(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, n: nat)
    requires 0 <= n < 256
    requires HashLength(algorithm) <= |key|
    ensures |T(algorithm, key, info, n)| == n * HashLength(algorithm)
    decreases algorithm, key, info, n
  {
  }

  lemma /*{:_induction algorithm, key, info, m, n}*/ TPrefix(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>, m: nat, n: nat)
    requires 0 <= m <= n < 256
    requires HashLength(algorithm) <= |key|
    ensures T(algorithm, key, info, m) <= T(algorithm, key, info, n)
    decreases algorithm, key, info, m, n
  {
  }

  function TMaxLength(algorithm: HMAC_ALGORITHM, key: seq<uint8>, info: seq<uint8>): (result: seq<uint8>)
    requires HashLength(algorithm) <= |key|
    ensures |result| == 255 * HashLength(algorithm)
    decreases algorithm, key, info
  {
    TLength(algorithm, key, info, 255);
    T(algorithm, key, info, 255)
  }
}
")]

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny
{
  using System.Collections.Generic;
  // set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;
#endif

  public class Set<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }
        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }
#else
    readonly HashSet<T> setImpl;
    Set(HashSet<T> s) {
      this.setImpl = s;
    }
    public static readonly Set<T> Empty = new Set<T>(new HashSet<T>());
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var s = new HashSet<T>(values);
      return new Set<T>(s);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var s = new HashSet<T>(values);
      s.Add(oneMoreValue);
      return new Set<T>(s);
    }
    public int Count {
      get { return this.setImpl.Count; }
    }
    public long LongCount {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
#endif

    public static Set<T> _DafnyDefaultValue() {
      return Empty;
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
#else
        var s = new HashSet<T>();
#endif
        while (true) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
#else
          yield return new Set<T>(new HashSet<T>(s));
#endif
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return containsNull == other.containsNull && this.setImpl.SetEquals(other.setImpl);
#else
      return this.setImpl.Count == other.setImpl.Count && IsSubsetOf(other);
#endif
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
#endif
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t)+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
#endif
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.Count < other.Count && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && !other.containsNull) {
        return false;
      }
#endif
      if (other.setImpl.Count < this.setImpl.Count)
        return false;
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && other.containsNull) {
        return false;
      }
      ImmutableHashSet<T> a, b;
#else
      HashSet<T> a, b;
#endif
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G t) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
#else
      return (t == null || t is T) && this.setImpl.Contains((T)(object)t);
#endif
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Set<T> Union(Set<T> other) {
      return new Set<T>(this.setImpl.Union(other.setImpl), containsNull || other.containsNull);
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl), containsNull && other.containsNull);
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl), containsNull && !other.containsNull);
    }
#else
    public Set<T> Union(Set<T> other) {
      if (this.setImpl.Count == 0)
        return other;
      else if (other.setImpl.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
#endif
  }

  public class MultiSet<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<T, BigInteger> dict;
#else
    readonly Dictionary<T, BigInteger> dict;
#endif
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);
#else
    MultiSet(Dictionary<T, BigInteger> d, BigInteger occurrencesOfNull) {
      this.dict = d;
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static MultiSet<T> Empty = new MultiSet<T>(new Dictionary<T, BigInteger>(0), BigInteger.Zero);
#endif
    public static MultiSet<T> FromElements(params T[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, BigInteger>(values.Length);
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, BigInteger>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, BigInteger>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, BigInteger>();
#endif
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }

    public static MultiSet<T> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      if (other.occurrencesOfNull < this.occurrencesOfNull) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      if (occurrencesOfNull > 0 && other.occurrencesOfNull > 0) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      } else if (t is T && dict.ContainsKey((T)(object)t)) {
        return dict[(T)(object)t];
      } else {
        return BigInteger.Zero;
      }
    }
    public MultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = dict;
#endif
        return new MultiSet<T>(r, i);
      } else {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = new Dictionary<T, BigInteger>(dict);
#endif
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count + occurrencesOfNull == 0)
        return other;
      else if (other.dict.Count + other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, BigInteger>();
#endif
      foreach (T t in dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r, occurrencesOfNull + other.occurrencesOfNull);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return other;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, BigInteger>();
#endif
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? other.occurrencesOfNull : occurrencesOfNull);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, BigInteger>();
#endif
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? occurrencesOfNull - other.occurrencesOfNull : BigInteger.Zero);
    }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var item in dict) {
          yield return item.Key;
        }
      }
    }
  }

  public class Map<U, V>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<U, V> dict;
#else
    readonly Dictionary<U, V> dict;
#endif
    readonly bool hasNullValue;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullValue", the value that "null" maps to

#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    Map(ImmutableDictionary<U, V>.Builder d, bool hasNullValue, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));
#else
    Map(Dictionary<U, V> d, bool hasNullValue, V nullValue) {
      this.dict = d;
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(new Dictionary<U, V>(), false, default(V));
#endif

    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Length);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<Pair<U, V>> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      // Initialize the capacity if the size of the enumerable is known
      Dictionary<U, V> d;
      if (values is ICollection<Pair<U, V>> collection) {
        d = new Dictionary<U, V>(collection.Count);
      } else {
        d = new Dictionary<U, V>();  
      }
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public int Count {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public static Map<U, V> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(Map<U, V> other) {
      if (hasNullValue != other.hasNullValue || dict.Count != other.dict.Count) {
        return false;
      } else if (hasNullValue && !object.Equals(nullValue, other.nullValue)) {
        return false;
      }
      foreach (U u in dict.Keys) {
        V v1 = dict[u];
        V v2;
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!object.Equals(v1, v2)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullValue) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullValue) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      if (hasNullValue && other.hasNullValue) {
        return false;
      }
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullValue : u is U && dict.ContainsKey((U)(object)u);
    }
    public V Select(U index) {
      // evidently, the following will throw some exception if "index" in not a key of the map
      return index == null && hasNullValue ? nullValue : dict[index];
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Map<U, V> Update(U index, V val) {
      var d = dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#else
    public Map<U, V> Update(U index, V val) {
      if (index == null) {
        return new Map<U, V>(dict, true, val);
      } else {
        var d = new Dictionary<U, V>(dict);
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#endif
    public Set<U> Keys {
      get {
        if (hasNullValue) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public Set<V> Values {
      get {
        if (hasNullValue) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }
    public Set<_System.Tuple2<U, V>> Items {
      get {
        HashSet<_System.Tuple2<U, V>> result = new HashSet<_System.Tuple2<U, V>>();
        if (hasNullValue) {
          result.Add(_System.Tuple2<U, V>.create(default(U), nullValue));
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          result.Add(_System.Tuple2<U, V>.create(kvp.Key, kvp.Value));
        }
        return Dafny.Set<_System.Tuple2<U, V>>.FromCollection(result);
      }
    }
  }

  public abstract class Sequence<T>
  {
    public static Sequence<T> Empty {
      get {
        return new ArraySequence<T>(new T[0]);
      }
    }
    public static Sequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static Sequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static Sequence<T> _DafnyDefaultValue() {
      return Empty;
    }
    public int Count {
      get { return (int)LongCount; }
    }
    public abstract long LongCount { get; }
    public abstract T[] Elements { get; }

    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(Elements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return Elements[index];
    }
    public T Select(long index) {
      return Elements[index];
    }
    public T Select(uint index) {
      return Elements[index];
    }
    public T Select(int index) {
      return Elements[index];
    }
    public T Select(BigInteger index) {
      return Elements[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])Elements.Clone();
      a[index] = t;
      return new ArraySequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = Elements.Length;
      return n == other.Elements.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      T[] elmts = Elements;
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (Elements is char[]) {
        var s = "";
        foreach (var t in Elements) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in Elements) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    bool EqualUntil(Sequence<T> other, int n) {
      T[] elmts = Elements, otherElmts = other.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(elmts[i], otherElmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = Elements.Length;
      return n < other.Elements.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = Elements.Length;
      return n <= other.Elements.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (Count == 0)
        return other;
      else if (other.Count == 0)
        return this;
      return new ConcatSequence<T>(this, other);
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        var elmts = Elements;
        int n = elmts.Length;
        for (int i = 0; i < n; i++) {
          if (object.Equals(t, elmts[i]))
            return true;
        }
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (Elements.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(Elements, a, m);
      return new ArraySequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[Elements.Length - m];
      System.Array.Copy(Elements, m, a, 0, Elements.Length - m);
      return new ArraySequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
    public Sequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Elements.Length) {
        return this;
      }
      T[] a = new T[hi - lo];
      System.Array.Copy(Elements, lo, a, 0, hi - lo);
      return new ArraySequence<T>(a);
    }
    public Sequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public Sequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public Sequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public Sequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public Sequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public Sequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public Sequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public Sequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }
  internal class ArraySequence<T> : Sequence<T> {
    private readonly T[] elmts;

    internal ArraySequence(T[] ee) {
      elmts = ee;
    }
    public override T[] Elements {
      get {
        return elmts;
      }
    }
    public override long LongCount {
      get {
        return elmts.LongLength;
      }
    }
  }
  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts == null or
    // left == null, right == null, and elmts != null
    private Sequence<T> left, right;
    private T[] elmts = null;
    private readonly long count;

    internal ConcatSequence(Sequence<T> left, Sequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.LongCount + right.LongCount;
    }

    public override T[] Elements {
      get {
        if (elmts == null) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override long LongCount {
      get {
        return count;
      }
    }

    private T[] ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences

      var ans = new T[count];
      var nextIndex = 0L;

      var toVisit = new Stack<Sequence<T>>();
      toVisit.Push(right);
      toVisit.Push(left);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        var cs = seq as ConcatSequence<T>;
        if (cs != null && cs.elmts == null) {
          toVisit.Push(cs.right);
          toVisit.Push(cs.left);
        } else {
          var array = seq.Elements;
          array.CopyTo(ans, nextIndex);
          nextIndex += array.LongLength;
        }
      }

      return ans;
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    [Obsolete("Use object.Equals(object, object) instead.")]
    public static bool AreEqual<G>(G a, G b) {
      return object.Equals(a, b);
    }
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }
    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }
    public static G Default<G>() {
      System.Type ty = typeof(G);
      System.Reflection.MethodInfo mInfo = ty.GetMethod("_DafnyDefaultValue");
      if (mInfo != null) {
        G g = (G)mInfo.Invoke(null, null);
        return g;
      } else {
        return default(G);
      }
    }
    // Computing forall/exists quantifiers
    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1);; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }
}

namespace @_System
{
  public class Tuple2<T0,T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.@Tuple2<T0,T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    static Tuple2<T0,T1> theDefault;
    public static Tuple2<T0,T1> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@Tuple2<T0,T1>(Dafny.Helpers.Default<T0>(), Dafny.Helpers.Default<T1>());
        }
        return theDefault;
      }
    }
    public static Tuple2<T0,T1> _DafnyDefaultValue() { return Default; }
    public static Tuple2<T0,T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0,T1>(_0, _1);
    }
    public bool is____hMake3 { get { return true; } }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
T[] a = new T[s0];
for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
namespace _System {


  public partial class nat {
  }

  public class Tuple0 {
    public Tuple0() {
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    static Tuple0 theDefault;
public static Tuple0 Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.Tuple0();
        }
        return theDefault;
      }
    }
    public static Tuple0 _DafnyDefaultValue() { return Default; }
public static Tuple0 create() {
      return new Tuple0();
    }
    public bool is____hMake0 { get { return true; } }
public static System.Collections.Generic.IEnumerable<Tuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }

  public class Tuple3<T0,T1,T2> {
    public readonly T0 _0;
public readonly T1 _1;
public readonly T2 _2;
public Tuple3(T0 _0, T1 _1, T2 _2) {
      this._0 = _0;
this._1 = _1;
this._2 = _2;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0,T1,T2>;
return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
return (int) hash;
    }
    public override string ToString() {
      string s = "";
s += "(";
s += Dafny.Helpers.ToString(this._0);
s += ", ";
s += Dafny.Helpers.ToString(this._1);
s += ", ";
s += Dafny.Helpers.ToString(this._2);
s += ")";
return s;
    }
    static Tuple3<T0,T1,T2> theDefault;
public static Tuple3<T0,T1,T2> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.Tuple3<T0,T1,T2>(Dafny.Helpers.Default<T0>(), Dafny.Helpers.Default<T1>(), Dafny.Helpers.Default<T2>());
        }
        return theDefault;
      }
    }
    public static Tuple3<T0,T1,T2> _DafnyDefaultValue() { return Default; }
public static Tuple3<T0,T1,T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0,T1,T2>(_0, _1, _2);
    }
    public bool is____hMake3 { get { return true; } }
public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
  }

  public class Tuple4<T0,T1,T2,T3> {
    public readonly T0 _0;
public readonly T1 _1;
public readonly T2 _2;
public readonly T3 _3;
public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this._0 = _0;
this._1 = _1;
this._2 = _2;
this._3 = _3;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0,T1,T2,T3>;
return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
return (int) hash;
    }
    public override string ToString() {
      string s = "";
s += "(";
s += Dafny.Helpers.ToString(this._0);
s += ", ";
s += Dafny.Helpers.ToString(this._1);
s += ", ";
s += Dafny.Helpers.ToString(this._2);
s += ", ";
s += Dafny.Helpers.ToString(this._3);
s += ")";
return s;
    }
    static Tuple4<T0,T1,T2,T3> theDefault;
public static Tuple4<T0,T1,T2,T3> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.Tuple4<T0,T1,T2,T3>(Dafny.Helpers.Default<T0>(), Dafny.Helpers.Default<T1>(), Dafny.Helpers.Default<T2>(), Dafny.Helpers.Default<T3>());
        }
        return theDefault;
      }
    }
    public static Tuple4<T0,T1,T2,T3> _DafnyDefaultValue() { return Default; }
public static Tuple4<T0,T1,T2,T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0,T1,T2,T3>(_0, _1, _2, _3);
    }
    public bool is____hMake4 { get { return true; } }
public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
  }







} // end of namespace _System
namespace STLUInt {

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
  }

  public partial class __default {
    public static Dafny.Sequence<byte> UInt16ToSeq(ushort x) {
      byte _539_b0 = (byte)((ushort)((x) / (256)));
byte _540_b1 = (byte)((ushort)((x) % (256)));
return Dafny.Sequence<byte>.FromElements(_539_b0, _540_b1);
    }
    public static ushort SeqToUInt16(Dafny.Sequence<byte> s) {
      BigInteger _541_x0 = (new BigInteger((s).Select(BigInteger.Zero))) * (new BigInteger(256));
BigInteger _542_x = (_541_x0) + (new BigInteger((s).Select(BigInteger.One)));
return (ushort)(_542_x);
    }
    public static byte[] UInt16ToArray(ushort x)
    {
    TAIL_CALL_START: ;
byte[] ret = new byte[0];
      var _nw0 = new byte[(int)(new BigInteger(2))];
      ret = _nw0;
      (ret)[(int)((BigInteger.Zero))] = (byte)((ushort)((x) / (256)));
      (ret)[(int)((BigInteger.One))] = (byte)((ushort)((x) % (256)));
      return ret;
    }
    public static ushort ArrayToUInt16(byte[] a) {
      BigInteger _543_x0 = (new BigInteger((a)[(int)(BigInteger.Zero)])) * (new BigInteger(256));
BigInteger _544_x = (_543_x0) + (new BigInteger((a)[(int)(BigInteger.One)]));
return (ushort)(_544_x);
    }
    public static Dafny.Sequence<byte> UInt32ToSeq(uint x) {
      byte _545_b0 = (byte)((x) / (16777216U));
uint _546_x0 = (x) - (((uint)(_545_b0)) * (16777216U));
byte _547_b1 = (byte)((_546_x0) / (65536U));
uint _548_x1 = (_546_x0) - (((uint)(_547_b1)) * (65536U));
byte _549_b2 = (byte)((_548_x1) / (256U));
byte _550_b3 = (byte)((_548_x1) % (256U));
return Dafny.Sequence<byte>.FromElements(_545_b0, _547_b1, _549_b2, _550_b3);
    }
    public static uint SeqToUInt32(Dafny.Sequence<byte> s) {
      BigInteger _551_x0 = (new BigInteger((s).Select(BigInteger.Zero))) * (new BigInteger(16777216));
BigInteger _552_x1 = (_551_x0) + ((new BigInteger((s).Select(BigInteger.One))) * (new BigInteger(65536)));
BigInteger _553_x2 = (_552_x1) + ((new BigInteger((s).Select(new BigInteger(2)))) * (new BigInteger(256)));
BigInteger _554_x = (_553_x2) + (new BigInteger((s).Select(new BigInteger(3))));
return (uint)(_554_x);
    }
    public static byte[] UInt32ToArray(uint x)
    {
    TAIL_CALL_START: ;
byte[] ret = new byte[0];
      uint _555_x_k;
      _555_x_k = x;
      var _nw1 = new byte[(int)(new BigInteger(4))];
      ret = _nw1;
      (ret)[(int)((BigInteger.Zero))] = (byte)((_555_x_k) / (16777216U));
      _555_x_k = (_555_x_k) - (((uint)((ret)[(int)(BigInteger.Zero)])) * (16777216U));
      (ret)[(int)((BigInteger.One))] = (byte)((_555_x_k) / (65536U));
      _555_x_k = (_555_x_k) - (((uint)((ret)[(int)(BigInteger.One)])) * (65536U));
      (ret)[(int)((new BigInteger(2)))] = (byte)((_555_x_k) / (256U));
      (ret)[(int)((new BigInteger(3)))] = (byte)((_555_x_k) % (256U));
      return ret;
    }
    public static uint ArrayToUInt32(byte[] a) {
      BigInteger _556_x0 = (new BigInteger((a)[(int)(BigInteger.Zero)])) * (new BigInteger(16777216));
BigInteger _557_x1 = (_556_x0) + ((new BigInteger((a)[(int)(BigInteger.One)])) * (new BigInteger(65536)));
BigInteger _558_x2 = (_557_x1) + ((new BigInteger((a)[(int)(new BigInteger(2))])) * (new BigInteger(256)));
BigInteger _559_x = (_558_x2) + (new BigInteger((a)[(int)(new BigInteger(3))]));
return (uint)(_559_x);
    }
    public static Dafny.Sequence<byte> UInt64ToSeq(ulong x) {
      ulong _560_bv = (ulong)(x);
byte _561_b0 = (byte)((_560_bv) >> (int)(new BigInteger(56)));
byte _562_b1 = (byte)(((_560_bv) >> (int)(new BigInteger(48))) & (255UL));
byte _563_b2 = (byte)(((_560_bv) >> (int)(new BigInteger(40))) & (255UL));
byte _564_b3 = (byte)(((_560_bv) >> (int)(new BigInteger(32))) & (255UL));
byte _565_b4 = (byte)(((_560_bv) >> (int)(new BigInteger(24))) & (255UL));
byte _566_b5 = (byte)(((_560_bv) >> (int)(new BigInteger(16))) & (255UL));
byte _567_b6 = (byte)(((_560_bv) >> (int)(new BigInteger(8))) & (255UL));
byte _568_b7 = (byte)((_560_bv) & (255UL));
return Dafny.Sequence<byte>.FromElements(_561_b0, _562_b1, _563_b2, _564_b3, _565_b4, _566_b5, _567_b6, _568_b7);
    }
    public static ulong SeqToUInt64(Dafny.Sequence<byte> s) {
      return (ulong)((((((((unchecked((ulong)((((ulong)((s).Select(BigInteger.Zero))) << (int)(new BigInteger(56)))))) | (unchecked((ulong)((((ulong)((s).Select(BigInteger.One))) << (int)(new BigInteger(48))))))) | (unchecked((ulong)((((ulong)((s).Select(new BigInteger(2)))) << (int)(new BigInteger(40))))))) | (unchecked((ulong)((((ulong)((s).Select(new BigInteger(3)))) << (int)(new BigInteger(32))))))) | (unchecked((ulong)((((ulong)((s).Select(new BigInteger(4)))) << (int)(new BigInteger(24))))))) | (unchecked((ulong)((((ulong)((s).Select(new BigInteger(5)))) << (int)(new BigInteger(16))))))) | (unchecked((ulong)((((ulong)((s).Select(new BigInteger(6)))) << (int)(new BigInteger(8))))))) | ((ulong)((s).Select(new BigInteger(7)))));
    }
    public static BigInteger UINT32__LIMIT { get {
      return new BigInteger(4294967296L);
    } }
    public static BigInteger UINT16__LIMIT { get {
      return new BigInteger(65536);
    } }
  }
} // end of namespace STLUInt
namespace STL {


  public abstract class Option<T> {
    public Option() { }
static Option<T> theDefault;
public static Option<T> Default {
      get {
        if (theDefault == null) {
          theDefault = new STL.Option_None<T>();
        }
        return theDefault;
      }
    }
    public static Option<T> _DafnyDefaultValue() { return Default; }
public static Option<T> create_None() {
      return new Option_None<T>();
    }
    public static Option<T> create_Some(T @get) {
      return new Option_Some<T>(@get);
    }
    public bool is_None { get { return this is Option_None<T>; } }
public bool is_Some { get { return this is Option_Some<T>; } }
public T dtor_get {
      get {
        var d = this;
return ((Option_Some<T>)d).@get; 
      }
    }
    public STL.Result<T> ToResult() {
      STL.Option<T> _source0 = this;
if (_source0.is_Some) {
        T _569_v = ((STL.Option_Some<T>)_source0).@get;
return @STL.Result<T>.create_Success(_569_v);
      } else {
        return @STL.Result<T>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      }
    }
    public T GetOrElse(T @default) {
      STL.Option<T> _source1 = this;
if (_source1.is_Some) {
        T _570_v = ((STL.Option_Some<T>)_source1).@get;
return _570_v;
      } else {
        return @default;
      }
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override bool Equals(object other) {
      var oth = other as STL.Option_None<T>;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Option.None";
return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T @get;
public Option_Some(T @get) {
      this.@get = @get;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Option_Some<T>;
return oth != null && object.Equals(this.@get, oth.@get);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@get));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Option.Some";
s += "(";
s += Dafny.Helpers.ToString(this.@get);
s += ")";
return s;
    }
  }

  public abstract class Either<S,T> {
    public Either() { }
static Either<S,T> theDefault;
public static Either<S,T> Default {
      get {
        if (theDefault == null) {
          theDefault = new STL.Either_Left<S,T>(Dafny.Helpers.Default<S>());
        }
        return theDefault;
      }
    }
    public static Either<S,T> _DafnyDefaultValue() { return Default; }
public static Either<S,T> create_Left(S left) {
      return new Either_Left<S,T>(left);
    }
    public static Either<S,T> create_Right(T right) {
      return new Either_Right<S,T>(right);
    }
    public bool is_Left { get { return this is Either_Left<S,T>; } }
public bool is_Right { get { return this is Either_Right<S,T>; } }
public S dtor_left {
      get {
        var d = this;
return ((Either_Left<S,T>)d).left; 
      }
    }
    public T dtor_right {
      get {
        var d = this;
return ((Either_Right<S,T>)d).right; 
      }
    }
  }
  public class Either_Left<S,T> : Either<S,T> {
    public readonly S left;
public Either_Left(S left) {
      this.left = left;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Either_Left<S,T>;
return oth != null && object.Equals(this.left, oth.left);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.left));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Either.Left";
s += "(";
s += Dafny.Helpers.ToString(this.left);
s += ")";
return s;
    }
  }
  public class Either_Right<S,T> : Either<S,T> {
    public readonly T right;
public Either_Right(T right) {
      this.right = right;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Either_Right<S,T>;
return oth != null && object.Equals(this.right, oth.right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.right));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Either.Right";
s += "(";
s += Dafny.Helpers.ToString(this.right);
s += ")";
return s;
    }
  }

  public abstract class Error {
    public Error() { }
static Error theDefault;
public static Error Default {
      get {
        if (theDefault == null) {
          theDefault = new STL.Error_IOError(Dafny.Sequence<char>.Empty);
        }
        return theDefault;
      }
    }
    public static Error _DafnyDefaultValue() { return Default; }
public static Error create_IOError(Dafny.Sequence<char> msg) {
      return new Error_IOError(msg);
    }
    public static Error create_DeserializationError(Dafny.Sequence<char> msg) {
      return new Error_DeserializationError(msg);
    }
    public static Error create_SerializationError(Dafny.Sequence<char> msg) {
      return new Error_SerializationError(msg);
    }
    public static Error create_Error(Dafny.Sequence<char> msg) {
      return new Error_Error(msg);
    }
    public bool is_IOError { get { return this is Error_IOError; } }
public bool is_DeserializationError { get { return this is Error_DeserializationError; } }
public bool is_SerializationError { get { return this is Error_SerializationError; } }
public bool is_Error { get { return this is Error_Error; } }
public Dafny.Sequence<char> dtor_msg {
      get {
        var d = this;
if (d is Error_IOError) { return ((Error_IOError)d).msg; }
if (d is Error_DeserializationError) { return ((Error_DeserializationError)d).msg; }
if (d is Error_SerializationError) { return ((Error_SerializationError)d).msg; }
return ((Error_Error)d).msg; 
      }
    }
  }
  public class Error_IOError : Error {
    public readonly Dafny.Sequence<char> msg;
public Error_IOError(Dafny.Sequence<char> msg) {
      this.msg = msg;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Error_IOError;
return oth != null && object.Equals(this.msg, oth.msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.msg));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Error.IOError";
s += "(";
s += Dafny.Helpers.ToString(this.msg);
s += ")";
return s;
    }
  }
  public class Error_DeserializationError : Error {
    public readonly Dafny.Sequence<char> msg;
public Error_DeserializationError(Dafny.Sequence<char> msg) {
      this.msg = msg;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Error_DeserializationError;
return oth != null && object.Equals(this.msg, oth.msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.msg));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Error.DeserializationError";
s += "(";
s += Dafny.Helpers.ToString(this.msg);
s += ")";
return s;
    }
  }
  public class Error_SerializationError : Error {
    public readonly Dafny.Sequence<char> msg;
public Error_SerializationError(Dafny.Sequence<char> msg) {
      this.msg = msg;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Error_SerializationError;
return oth != null && object.Equals(this.msg, oth.msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 2;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.msg));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Error.SerializationError";
s += "(";
s += Dafny.Helpers.ToString(this.msg);
s += ")";
return s;
    }
  }
  public class Error_Error : Error {
    public readonly Dafny.Sequence<char> msg;
public Error_Error(Dafny.Sequence<char> msg) {
      this.msg = msg;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Error_Error;
return oth != null && object.Equals(this.msg, oth.msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 3;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.msg));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Error.Error";
s += "(";
s += Dafny.Helpers.ToString(this.msg);
s += ")";
return s;
    }
  }

  public abstract class Result<T> {
    public Result() { }
static Result<T> theDefault;
public static Result<T> Default {
      get {
        if (theDefault == null) {
          theDefault = new STL.Result_Failure<T>(Dafny.Sequence<char>.Empty);
        }
        return theDefault;
      }
    }
    public static Result<T> _DafnyDefaultValue() { return Default; }
public static Result<T> create_Success(T @value) {
      return new Result_Success<T>(@value);
    }
    public static Result<T> create_Failure(Dafny.Sequence<char> error) {
      return new Result_Failure<T>(error);
    }
    public bool is_Success { get { return this is Result_Success<T>; } }
public bool is_Failure { get { return this is Result_Failure<T>; } }
public T dtor_value {
      get {
        var d = this;
return ((Result_Success<T>)d).@value; 
      }
    }
    public Dafny.Sequence<char> dtor_error {
      get {
        var d = this;
return ((Result_Failure<T>)d).error; 
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public STL.Result<U> PropagateFailure<U>() {
      return @STL.Result<U>.create_Failure((this).dtor_error);
    }
    public T Extract() {
      return (this).dtor_value;
    }
    public STL.Option<T> ToOption() {
      STL.Result<T> _source2 = this;
if (_source2.is_Success) {
        T _571_s = ((STL.Result_Success<T>)_source2).@value;
return @STL.Option<T>.create_Some(_571_s);
      } else {
        Dafny.Sequence<char> _572_e = ((STL.Result_Failure<T>)_source2).error;
return @STL.Option<T>.create_None();
      }
    }
    public T GetOrElse(T @default) {
      STL.Result<T> _source3 = this;
if (_source3.is_Success) {
        T _573_s = ((STL.Result_Success<T>)_source3).@value;
return _573_s;
      } else {
        Dafny.Sequence<char> _574_e = ((STL.Result_Failure<T>)_source3).error;
return @default;
      }
    }
  }
  public class Result_Success<T> : Result<T> {
    public readonly T @value;
public Result_Success(T @value) {
      this.@value = @value;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Result_Success<T>;
return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Result.Success";
s += "(";
s += Dafny.Helpers.ToString(this.@value);
s += ")";
return s;
    }
  }
  public class Result_Failure<T> : Result<T> {
    public readonly Dafny.Sequence<char> error;
public Result_Failure(Dafny.Sequence<char> error) {
      this.error = error;
    }
    public override bool Equals(object other) {
      var oth = other as STL.Result_Failure<T>;
return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
return (int) hash;
    }
    public override string ToString() {
      string s = "STL_Compile.Result.Failure";
s += "(";
s += Dafny.Helpers.ToString(this.error);
s += ")";
return s;
    }
  }

  public partial class mut<T> {
    public T x = Dafny.Helpers.Default<T>();
public void __ctor(T y)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).x = y;
    }
    public void put(T y)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).x = y;
    }
    public T @get() {
      return this.x;
    }
  }

  public partial class __default {
    public static STL.Result<_System.Tuple0> RequireEqual<T>(T expected, T actual)
    {
      return STL.__default.Require((expected).Equals((actual)));
    }
    public static STL.Result<_System.Tuple0> Require(bool b) {
      return STL.__default.RequireWithMessage(b, Dafny.Sequence<char>.FromString("Failed requirement"));
    }
    public static STL.Result<_System.Tuple0> RequireWithMessage(bool b, Dafny.Sequence<char> message)
    {
      if (b) {
        return @STL.Result<_System.Tuple0>.create_Success(@_System.Tuple0.create());
      } else  {
        return @STL.Result<_System.Tuple0>.create_Failure(message);
      }
    }
    public static Dafny.Sequence<T> Join<T>(Dafny.Sequence<Dafny.Sequence<T>> ss, Dafny.Sequence<T> joiner)
    {
      if ((new BigInteger((ss).Count)) == (BigInteger.One)) {
        return (ss).Select(BigInteger.Zero);
      } else  {
        return (((ss).Select(BigInteger.Zero)).Concat((joiner))).Concat((STL.__default.Join<T>((ss).Drop(BigInteger.One), joiner)));
      }
    }
    public static Dafny.Sequence<Dafny.Sequence<T>> Split<T>(Dafny.Sequence<T> s, T delim)
    {
      STL.Option<BigInteger> _575_i = STL.__default.Find<T>(s, delim, BigInteger.Zero);
if ((_575_i).is_Some) {
        return (Dafny.Sequence<Dafny.Sequence<T>>.FromElements((s).Take((_575_i).dtor_get))).Concat((STL.__default.Split<T>((s).Drop(((_575_i).dtor_get) + (BigInteger.One)), delim)));
      } else  {
        return Dafny.Sequence<Dafny.Sequence<T>>.FromElements(s);
      }
    }
    public static STL.Option<BigInteger> Find<T>(Dafny.Sequence<T> s, T c, BigInteger i)
    {
      if ((i) == (new BigInteger((s).Count))) {
        return @STL.Option<BigInteger>.create_None();
      } else  {
        if (((s).Select(i)).Equals((c))) {
          return @STL.Option<BigInteger>.create_Some(i);
        } else  {
          return STL.__default.Find<T>(s, c, (i) + (BigInteger.One));
        }
      }
    }
    public static T[] SeqToArray<T>(Dafny.Sequence<T> s)
    {
    TAIL_CALL_START: ;
T[] a = new T[0];
      var _nw2 = new T[(int)(new BigInteger((s).Count))];
var _arrayinit0 = Dafny.Helpers.Id<Func<Dafny.Sequence<T>,Func<BigInteger,T>>>((_576_s) => ((System.Func<BigInteger, T>)((_577_i) => {
        return (_576_s).Select(_577_i);
      })))(s);
for (var _arrayinit_00 = 0; _arrayinit_00 < _nw2.Length; _arrayinit_00++) {
        _nw2[(int)(_arrayinit_00)] = _arrayinit0(_arrayinit_00);
      }
      a = _nw2;
      return a;
    }
    public static byte[] StringToByteArray(Dafny.Sequence<char> s)
    {
    TAIL_CALL_START: ;
byte[] a = new byte[0];
      var _nw3 = new byte[(int)(new BigInteger((s).Count))];
      a = _nw3;
      foreach (var _578_i in Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((s).Count))) {
        if ((true) && (((_578_i).Sign != -1) && ((_578_i) < (new BigInteger((s).Count))))) {
          (a)[(int)((_578_i))] = (byte)(Dafny.Helpers.EuclideanModulus(new BigInteger((s).Select(_578_i)), new BigInteger(256)));
        }
      }
      return a;
    }
    public static bool uniq<T>(Dafny.Sequence<T> s) {
      if ((s).Equals((Dafny.Sequence<T>.FromElements()))) {
        return true;
      } else  {
        if (((s).Drop(BigInteger.One)).Contains(((s).Select(BigInteger.Zero)))) {
          return false;
        } else  {
          return STL.__default.uniq<T>((s).Drop(BigInteger.One));
        }
      }
    }
    public static BigInteger sum<T>(Dafny.Sequence<T> s, Func<T,BigInteger> f)
    {
      if ((s).Equals((Dafny.Sequence<T>.FromElements()))) {
        return BigInteger.Zero;
      } else  {
        return (Dafny.Helpers.Id<Func<T,BigInteger>>(f)((s).Select(BigInteger.Zero))) + (STL.__default.sum<T>((s).Drop(BigInteger.One), f));
      }
    }
    public static Dafny.Sequence<T> MapSeq<S,T>(Dafny.Sequence<S> s, Func<S,T> f)
    {
      if ((s).Equals((Dafny.Sequence<S>.FromElements()))) {
        return Dafny.Sequence<T>.FromElements();
      } else  {
        return (Dafny.Sequence<T>.FromElements(Dafny.Helpers.Id<Func<S,T>>(f)((s).Select(BigInteger.Zero)))).Concat((STL.__default.MapSeq<S,T>((s).Drop(BigInteger.One), f)));
      }
    }
    public static Dafny.Sequence<T> FlattenSeq<T>(Dafny.Sequence<Dafny.Sequence<T>> s) {
      if ((s).Equals((Dafny.Sequence<Dafny.Sequence<T>>.FromElements()))) {
        return Dafny.Sequence<T>.FromElements();
      } else  {
        return ((s).Select(BigInteger.Zero)).Concat((STL.__default.FlattenSeq<T>((s).Drop(BigInteger.One))));
      }
    }
    public static bool uniq__fst<S,T>(Dafny.Sequence<_System.Tuple2<S,T>> s) {
      return STL.__default.uniq<S>(STL.__default.MapSeq<_System.Tuple2<S,T>,S>(s, Dafny.Helpers.Id<Func<Func<_System.Tuple2<S,T>,S>>>(() => ((System.Func<_System.Tuple2<S,T>, S>)((_579_x) => {
        return (_579_x).dtor__0;
      })))()));
    }
    public static BigInteger min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else  {
        return b;
      }
    }
    public static Dafny.Sequence<B> values<A,B>(Dafny.Map<A,B> m)
    {
    TAIL_CALL_START: ;
Dafny.Sequence<B> vals = Dafny.Sequence<B>.Empty;
      Dafny.Set<A> _580_keys;
      _580_keys = (m).Keys;
      vals = Dafny.Sequence<B>.FromElements();
      while (!(_580_keys).Equals((Dafny.Set<A>.FromElements()))) {
        A _581_a;
        foreach (var _assign_such_that_0 in (_580_keys).Elements) { _581_a = _assign_such_that_0;
          if ((_580_keys).Contains((_581_a))) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 355)");
      after__ASSIGN_SUCH_THAT_0: ;
        _580_keys = (_580_keys).Difference((Dafny.Set<A>.FromElements(_581_a)));
        vals = (vals).Concat((Dafny.Sequence<B>.FromElements((m).Select(_581_a))));
      }
      return vals;
    }
    public static bool UInt8Less(byte a, byte b)
    {
      return (a) < (b);
    }
    public static bool NatLess(BigInteger a, BigInteger b)
    {
      return (a) < (b);
    }
    public static bool IntLess(BigInteger a, BigInteger b)
    {
      return (a) < (b);
    }
    public static bool LexicographicLessOrEqual<T>(Dafny.Sequence<T> a, Dafny.Sequence<T> b, Func<T,T,bool> less)
    {
      return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, (new BigInteger((a).Count)) + (BigInteger.One)), false, (((_582_k) => {
        return (((_582_k).Sign != -1) && ((_582_k) <= (new BigInteger((a).Count)))) && (STL.__default.LexicographicLessOrEqualAux<T>(a, b, less, _582_k));
      })));
    }
    public static bool LexicographicLessOrEqualAux<T>(Dafny.Sequence<T> a, Dafny.Sequence<T> b, Func<T,T,bool> less, BigInteger lengthOfCommonPrefix)
    {
      return (((lengthOfCommonPrefix) <= (new BigInteger((b).Count))) && (Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, lengthOfCommonPrefix), true, (((_583_i) => {
        return !(((_583_i).Sign != -1) && ((_583_i) < (lengthOfCommonPrefix))) || (((a).Select(_583_i)).Equals(((b).Select(_583_i))));
      }))))) && (((lengthOfCommonPrefix) == (new BigInteger((a).Count))) || (((lengthOfCommonPrefix) < (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<T,T,bool>>(less)((a).Select(lengthOfCommonPrefix), (b).Select(lengthOfCommonPrefix)))));
    }
    public static Dafny.Sequence<T> Filter<T>(Dafny.Sequence<T> s, Func<T,bool> f)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<T>.FromElements();
      } else  {
        if (Dafny.Helpers.Id<Func<T,bool>>(f)((s).Select(BigInteger.Zero))) {
          return (Dafny.Sequence<T>.FromElements((s).Select(BigInteger.Zero))).Concat((STL.__default.Filter<T>((s).Drop(BigInteger.One), f)));
        } else  {
          return STL.__default.Filter<T>((s).Drop(BigInteger.One), f);
        }
      }
    }
  }

} // end of namespace STL
namespace UTF8 {



  public partial class ValidUTF8Bytes {
    public static readonly Dafny.Sequence<byte> Witness = Dafny.Sequence<byte>.FromElements();
  }

  public partial class __default {
    public static bool IsASCIIString(Dafny.Sequence<char> s) {
      return Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((s).Count)), true, (((_584_i) => {
        return !(((_584_i).Sign != -1) && ((_584_i) < (new BigInteger((s).Count)))) || ((new BigInteger((s).Select(_584_i))) < (new BigInteger(128)));
      })));
    }
    public static bool BitAt(byte x, byte idx)
    {
      byte _585_w = (byte)(x);
return ((byte)(((byte)((_585_w) >> (int)(idx))) & (1))) == (1);
    }
    public static bool ValidUTF8Continuation(Dafny.Sequence<byte> a, BigInteger offset)
    {
      return (UTF8.__default.BitAt((a).Select(offset), 7)) && (!(UTF8.__default.BitAt((a).Select(offset), 6)));
    }
    public static byte CodePointCase(Dafny.Sequence<byte> a, BigInteger offset)
    {
      if (UTF8.__default.BitAt((a).Select(offset), 7)) {
        if (UTF8.__default.BitAt((a).Select(offset), 6)) {
          if (UTF8.__default.BitAt((a).Select(offset), 5)) {
            if (UTF8.__default.BitAt((a).Select(offset), 4)) {
              if (UTF8.__default.BitAt((a).Select(offset), 3)) {
                return 0;
              } else  {
                return 4;
              }
            } else  {
              return 3;
            }
          } else  {
            return 2;
          }
        } else  {
          return 0;
        }
      } else  {
        return 1;
      }
    }
    public static bool ValidUTF8__at(Dafny.Sequence<byte> a, BigInteger offset)
    {
      if ((offset) == (new BigInteger((a).Count))) {
        return true;
      } else  {
        byte _586_c = UTF8.__default.CodePointCase(a, offset);
if ((_586_c) == (1)) {
          return UTF8.__default.ValidUTF8__at(a, (offset) + (BigInteger.One));
        } else  {
          if ((_586_c) == (2)) {
            return ((((offset) + (new BigInteger(2))) <= (new BigInteger((a).Count))) && (UTF8.__default.ValidUTF8Continuation(a, (offset) + (BigInteger.One)))) && (UTF8.__default.ValidUTF8__at(a, (offset) + (new BigInteger(2))));
          } else  {
            if ((_586_c) == (3)) {
              return (((((offset) + (new BigInteger(3))) <= (new BigInteger((a).Count))) && (UTF8.__default.ValidUTF8Continuation(a, (offset) + (BigInteger.One)))) && (UTF8.__default.ValidUTF8Continuation(a, (offset) + (new BigInteger(2))))) && (UTF8.__default.ValidUTF8__at(a, (offset) + (new BigInteger(3))));
            } else  {
              if ((_586_c) == (4)) {
                return ((((((offset) + (new BigInteger(4))) <= (new BigInteger((a).Count))) && (UTF8.__default.ValidUTF8Continuation(a, (offset) + (BigInteger.One)))) && (UTF8.__default.ValidUTF8Continuation(a, (offset) + (new BigInteger(2))))) && (UTF8.__default.ValidUTF8Continuation(a, (offset) + (new BigInteger(3))))) && (UTF8.__default.ValidUTF8__at(a, (offset) + (new BigInteger(4))));
              } else  {
                return false;
              }
            }
          }
        }
      }
    }
    public static bool ValidUTF8(byte[] a) {
      return UTF8.__default.ValidUTF8__at(Dafny.Helpers.SeqFromArray(a), BigInteger.Zero);
    }
    public static bool ValidUTF8Seq(Dafny.Sequence<byte> s) {
      return UTF8.__default.ValidUTF8__at(s, BigInteger.Zero);
    }
  }
} // end of namespace UTF8
namespace EncryptionSuites {



  public class EncryptionAlgorithm {
    public readonly EncryptionSuites.AESMode mode;
public EncryptionAlgorithm(EncryptionSuites.AESMode mode) {
      this.mode = mode;
    }
    public override bool Equals(object other) {
      var oth = other as EncryptionSuites.EncryptionAlgorithm;
return oth != null && object.Equals(this.mode, oth.mode);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.mode));
return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptionSuites_Compile.EncryptionAlgorithm.AES";
s += "(";
s += Dafny.Helpers.ToString(this.mode);
s += ")";
return s;
    }
    static EncryptionAlgorithm theDefault;
public static EncryptionAlgorithm Default {
      get {
        if (theDefault == null) {
          theDefault = new EncryptionSuites.EncryptionAlgorithm(EncryptionSuites.AESMode.Default);
        }
        return theDefault;
      }
    }
    public static EncryptionAlgorithm _DafnyDefaultValue() { return Default; }
public static EncryptionAlgorithm create(EncryptionSuites.AESMode mode) {
      return new EncryptionAlgorithm(mode);
    }
    public bool is_AES { get { return true; } }
public EncryptionSuites.AESMode dtor_mode {
      get {
        return this.mode;
      }
    }
  }

  public class AESMode {
    public AESMode() {
    }
    public override bool Equals(object other) {
      var oth = other as EncryptionSuites.AESMode;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptionSuites_Compile.AESMode.GCM";
return s;
    }
    static AESMode theDefault;
public static AESMode Default {
      get {
        if (theDefault == null) {
          theDefault = new EncryptionSuites.AESMode();
        }
        return theDefault;
      }
    }
    public static AESMode _DafnyDefaultValue() { return Default; }
public static AESMode create() {
      return new AESMode();
    }
    public bool is_GCM { get { return true; } }
public static System.Collections.Generic.IEnumerable<AESMode> AllSingletonConstructors {
      get {
        yield return AESMode.create();
      }
    }
  }

  public class EncryptionSuite {
    public readonly EncryptionSuites.EncryptionAlgorithm alg;
public readonly byte keyLen;
public readonly byte tagLen;
public readonly byte ivLen;
public EncryptionSuite(EncryptionSuites.EncryptionAlgorithm alg, byte keyLen, byte tagLen, byte ivLen) {
      this.alg = alg;
this.keyLen = keyLen;
this.tagLen = tagLen;
this.ivLen = ivLen;
    }
    public override bool Equals(object other) {
      var oth = other as EncryptionSuites.EncryptionSuite;
return oth != null && object.Equals(this.alg, oth.alg) && this.keyLen == oth.keyLen && this.tagLen == oth.tagLen && this.ivLen == oth.ivLen;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.alg));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyLen));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.tagLen));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ivLen));
return (int) hash;
    }
    public override string ToString() {
      string s = "EncryptionSuites_Compile.EncryptionSuite.EncryptionSuite";
s += "(";
s += Dafny.Helpers.ToString(this.alg);
s += ", ";
s += Dafny.Helpers.ToString(this.keyLen);
s += ", ";
s += Dafny.Helpers.ToString(this.tagLen);
s += ", ";
s += Dafny.Helpers.ToString(this.ivLen);
s += ")";
return s;
    }
    static EncryptionSuite theDefault;
public static EncryptionSuite Default {
      get {
        if (theDefault == null) {
          theDefault = new EncryptionSuites.EncryptionSuite(EncryptionSuites.EncryptionAlgorithm.Default, 0, 0, 0);
        }
        return theDefault;
      }
    }
    public static EncryptionSuite _DafnyDefaultValue() { return Default; }
public static EncryptionSuite create(EncryptionSuites.EncryptionAlgorithm alg, byte keyLen, byte tagLen, byte ivLen) {
      return new EncryptionSuite(alg, keyLen, tagLen, ivLen);
    }
    public bool is_EncryptionSuite { get { return true; } }
public EncryptionSuites.EncryptionAlgorithm dtor_alg {
      get {
        return this.alg;
      }
    }
    public byte dtor_keyLen {
      get {
        return this.keyLen;
      }
    }
    public byte dtor_tagLen {
      get {
        return this.tagLen;
      }
    }
    public byte dtor_ivLen {
      get {
        return this.ivLen;
      }
    }
  }

  public partial class __default {
    public static byte AES__TAG__LEN { get {
      return (byte)(16);
    } }
    public static byte AES__IV__LEN { get {
      return (byte)(12);
    } }
    public static EncryptionSuites.EncryptionSuite AES__GCM__128 { get {
      return @EncryptionSuites.EncryptionSuite.create(@EncryptionSuites.EncryptionAlgorithm.create(@EncryptionSuites.AESMode.create()), 16, EncryptionSuites.__default.AES__TAG__LEN, EncryptionSuites.__default.AES__IV__LEN);
    } }
    public static EncryptionSuites.EncryptionSuite AES__GCM__192 { get {
      return @EncryptionSuites.EncryptionSuite.create(@EncryptionSuites.EncryptionAlgorithm.create(@EncryptionSuites.AESMode.create()), 24, EncryptionSuites.__default.AES__TAG__LEN, EncryptionSuites.__default.AES__IV__LEN);
    } }
    public static EncryptionSuites.EncryptionSuite AES__GCM__256 { get {
      return @EncryptionSuites.EncryptionSuite.create(@EncryptionSuites.EncryptionAlgorithm.create(@EncryptionSuites.AESMode.create()), 32, EncryptionSuites.__default.AES__TAG__LEN, EncryptionSuites.__default.AES__IV__LEN);
    } }
    public static Dafny.Set<BigInteger> AES__CIPHER__KEY__LENGTHS { get {
      return Dafny.Set<BigInteger>.FromElements(new BigInteger(32), new BigInteger(24), new BigInteger(16));
    } }
    public static BigInteger AES__MAX__KEY__LEN { get {
      return new BigInteger(32);
    } }
  }
} // end of namespace EncryptionSuites
namespace Signature {



  public abstract class ECDSAParams {
    public ECDSAParams() { }
static ECDSAParams theDefault;
public static ECDSAParams Default {
      get {
        if (theDefault == null) {
          theDefault = new Signature.ECDSAParams_ECDSA__P384();
        }
        return theDefault;
      }
    }
    public static ECDSAParams _DafnyDefaultValue() { return Default; }
public static ECDSAParams create_ECDSA__P384() {
      return new ECDSAParams_ECDSA__P384();
    }
    public static ECDSAParams create_ECDSA__P256() {
      return new ECDSAParams_ECDSA__P256();
    }
    public bool is_ECDSA__P384 { get { return this is ECDSAParams_ECDSA__P384; } }
public bool is_ECDSA__P256 { get { return this is ECDSAParams_ECDSA__P256; } }
public static System.Collections.Generic.IEnumerable<ECDSAParams> AllSingletonConstructors {
      get {
        yield return ECDSAParams.create_ECDSA__P384();
yield return ECDSAParams.create_ECDSA__P256();
      }
    }
    public ushort SignatureLength() {
      Signature.ECDSAParams _source4 = this;
if (_source4.is_ECDSA__P256) {
        return 71;
      } else {
        return 103;
      }
    }
  }
  public class ECDSAParams_ECDSA__P384 : ECDSAParams {
    public ECDSAParams_ECDSA__P384() {
    }
    public override bool Equals(object other) {
      var oth = other as Signature.ECDSAParams_ECDSA__P384;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.ECDSAParams.ECDSA_P384";
return s;
    }
  }
  public class ECDSAParams_ECDSA__P256 : ECDSAParams {
    public ECDSAParams_ECDSA__P256() {
    }
    public override bool Equals(object other) {
      var oth = other as Signature.ECDSAParams_ECDSA__P256;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
return (int) hash;
    }
    public override string ToString() {
      string s = "Signature_Compile.ECDSAParams.ECDSA_P256";
return s;
    }
  }



} // end of namespace Signature
namespace Digests {



  public abstract class HMAC_ALGORITHM {
    public HMAC_ALGORITHM() { }
static HMAC_ALGORITHM theDefault;
public static HMAC_ALGORITHM Default {
      get {
        if (theDefault == null) {
          theDefault = new Digests.HMAC_ALGORITHM_HmacSHA256();
        }
        return theDefault;
      }
    }
    public static HMAC_ALGORITHM _DafnyDefaultValue() { return Default; }
public static HMAC_ALGORITHM create_HmacSHA256() {
      return new HMAC_ALGORITHM_HmacSHA256();
    }
    public static HMAC_ALGORITHM create_HmacSHA384() {
      return new HMAC_ALGORITHM_HmacSHA384();
    }
    public static HMAC_ALGORITHM create_HmacNOSHA() {
      return new HMAC_ALGORITHM_HmacNOSHA();
    }
    public bool is_HmacSHA256 { get { return this is HMAC_ALGORITHM_HmacSHA256; } }
public bool is_HmacSHA384 { get { return this is HMAC_ALGORITHM_HmacSHA384; } }
public bool is_HmacNOSHA { get { return this is HMAC_ALGORITHM_HmacNOSHA; } }
public static System.Collections.Generic.IEnumerable<HMAC_ALGORITHM> AllSingletonConstructors {
      get {
        yield return HMAC_ALGORITHM.create_HmacSHA256();
yield return HMAC_ALGORITHM.create_HmacSHA384();
yield return HMAC_ALGORITHM.create_HmacNOSHA();
      }
    }
  }
  public class HMAC_ALGORITHM_HmacSHA256 : HMAC_ALGORITHM {
    public HMAC_ALGORITHM_HmacSHA256() {
    }
    public override bool Equals(object other) {
      var oth = other as Digests.HMAC_ALGORITHM_HmacSHA256;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
return (int) hash;
    }
    public override string ToString() {
      string s = "Digests_Compile.HMAC_ALGORITHM.HmacSHA256";
return s;
    }
  }
  public class HMAC_ALGORITHM_HmacSHA384 : HMAC_ALGORITHM {
    public HMAC_ALGORITHM_HmacSHA384() {
    }
    public override bool Equals(object other) {
      var oth = other as Digests.HMAC_ALGORITHM_HmacSHA384;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
return (int) hash;
    }
    public override string ToString() {
      string s = "Digests_Compile.HMAC_ALGORITHM.HmacSHA384";
return s;
    }
  }
  public class HMAC_ALGORITHM_HmacNOSHA : HMAC_ALGORITHM {
    public HMAC_ALGORITHM_HmacNOSHA() {
    }
    public override bool Equals(object other) {
      var oth = other as Digests.HMAC_ALGORITHM_HmacNOSHA;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 2;
return (int) hash;
    }
    public override string ToString() {
      string s = "Digests_Compile.HMAC_ALGORITHM.HmacNOSHA";
return s;
    }
  }

} // end of namespace Digests
namespace _25_AlgorithmSuite_Compile {






  public partial class ID {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    public static readonly ushort Witness = (ushort)(20);
public static EncryptionSuites.EncryptionSuite EncryptionSuite(ushort _this) {
      return ((_25_AlgorithmSuite_Compile.__default.Suite).Select(_this)).dtor_algorithm;
    }
    public static BigInteger KeyLength(ushort _this) {
      return new BigInteger((((_25_AlgorithmSuite_Compile.__default.Suite).Select(_this)).dtor_algorithm).dtor_keyLen);
    }
    public static BigInteger KDFInputKeyLength(ushort _this) {
      return _25_AlgorithmSuite_Compile.ID.KeyLength(_this);
    }
    public static BigInteger IVLength(ushort _this) {
      return new BigInteger((((_25_AlgorithmSuite_Compile.__default.Suite).Select(_this)).dtor_algorithm).dtor_ivLen);
    }
    public static BigInteger TagLength(ushort _this) {
      return new BigInteger((((_25_AlgorithmSuite_Compile.__default.Suite).Select(_this)).dtor_algorithm).dtor_tagLen);
    }
    public static STL.Option<Signature.ECDSAParams> SignatureType(ushort _this) {
      return ((_25_AlgorithmSuite_Compile.__default.Suite).Select(_this)).dtor_sign;
    }
    public static bool ValidPlaintextDataKey(ushort _this, Dafny.Sequence<byte> plaintextDataKey) {
      return (new BigInteger((plaintextDataKey).Count)) == (_25_AlgorithmSuite_Compile.ID.KDFInputKeyLength(_this));
    }
  }

  public class AlgSuite {
    public readonly EncryptionSuites.EncryptionSuite algorithm;
public readonly Digests.HMAC_ALGORITHM hkdf;
public readonly STL.Option<Signature.ECDSAParams> sign;
public AlgSuite(EncryptionSuites.EncryptionSuite algorithm, Digests.HMAC_ALGORITHM hkdf, STL.Option<Signature.ECDSAParams> sign) {
      this.algorithm = algorithm;
this.hkdf = hkdf;
this.sign = sign;
    }
    public override bool Equals(object other) {
      var oth = other as _25_AlgorithmSuite_Compile.AlgSuite;
return oth != null && object.Equals(this.algorithm, oth.algorithm) && object.Equals(this.hkdf, oth.hkdf) && object.Equals(this.sign, oth.sign);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithm));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.hkdf));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.sign));
return (int) hash;
    }
    public override string ToString() {
      string s = "_25_AlgorithmSuite_Compile.AlgSuite.AlgSuite";
s += "(";
s += Dafny.Helpers.ToString(this.algorithm);
s += ", ";
s += Dafny.Helpers.ToString(this.hkdf);
s += ", ";
s += Dafny.Helpers.ToString(this.sign);
s += ")";
return s;
    }
    static AlgSuite theDefault;
public static AlgSuite Default {
      get {
        if (theDefault == null) {
          theDefault = new _25_AlgorithmSuite_Compile.AlgSuite(EncryptionSuites.EncryptionSuite.Default, Digests.HMAC_ALGORITHM.Default, STL.Option<Signature.ECDSAParams>.Default);
        }
        return theDefault;
      }
    }
    public static AlgSuite _DafnyDefaultValue() { return Default; }
public static AlgSuite create(EncryptionSuites.EncryptionSuite algorithm, Digests.HMAC_ALGORITHM hkdf, STL.Option<Signature.ECDSAParams> sign) {
      return new AlgSuite(algorithm, hkdf, sign);
    }
    public bool is_AlgSuite { get { return true; } }
public EncryptionSuites.EncryptionSuite dtor_algorithm {
      get {
        return this.algorithm;
      }
    }
    public Digests.HMAC_ALGORITHM dtor_hkdf {
      get {
        return this.hkdf;
      }
    }
    public STL.Option<Signature.ECDSAParams> dtor_sign {
      get {
        return this.sign;
      }
    }
  }

  public partial class __default {
    public static Dafny.Set<ushort> VALID__IDS { get {
      return Dafny.Set<ushort>.FromElements(888, 838, 532, 376, 326, 276, 120, 70, 20);
    } }
    public static ushort AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384 { get {
      return 888;
    } }
    public static ushort AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384 { get {
      return 838;
    } }
    public static ushort AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256 { get {
      return 532;
    } }
    public static ushort AES__256__GCM__IV12__TAG16__HKDF__SHA256__SIGNONE { get {
      return 376;
    } }
    public static ushort AES__192__GCM__IV12__TAG16__HKDF__SHA256__SIGNONE { get {
      return 326;
    } }
    public static ushort AES__128__GCM__IV12__TAG16__HKDF__SHA256__SIGNONE { get {
      return 276;
    } }
    public static ushort AES__256__GCM__IV12__TAG16__KDFNONE__SIGNONE { get {
      return 120;
    } }
    public static ushort AES__192__GCM__IV12__TAG16__KDFNONE__SIGNONE { get {
      return 70;
    } }
    public static ushort AES__128__GCM__IV12__TAG16__KDFNONE__SIGNONE { get {
      return 20;
    } }
    public static Dafny.Map<ushort,_25_AlgorithmSuite_Compile.AlgSuite> Suite { get {
      return Dafny.Map<ushort,_25_AlgorithmSuite_Compile.AlgSuite>.FromElements(new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__256, @Digests.HMAC_ALGORITHM.create_HmacSHA384(), @STL.Option<Signature.ECDSAParams>.create_Some(@Signature.ECDSAParams.create_ECDSA__P384()))), new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__192__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__192, @Digests.HMAC_ALGORITHM.create_HmacSHA384(), @STL.Option<Signature.ECDSAParams>.create_Some(@Signature.ECDSAParams.create_ECDSA__P384()))), new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__128__GCM__IV12__TAG16__HKDF__SHA256__ECDSA__P256,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__128, @Digests.HMAC_ALGORITHM.create_HmacSHA256(), @STL.Option<Signature.ECDSAParams>.create_Some(@Signature.ECDSAParams.create_ECDSA__P256()))), new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA256__SIGNONE,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__256, @Digests.HMAC_ALGORITHM.create_HmacSHA256(), @STL.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__192__GCM__IV12__TAG16__HKDF__SHA256__SIGNONE,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__192, @Digests.HMAC_ALGORITHM.create_HmacSHA256(), @STL.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__128__GCM__IV12__TAG16__HKDF__SHA256__SIGNONE,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__128, @Digests.HMAC_ALGORITHM.create_HmacSHA256(), @STL.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__256__GCM__IV12__TAG16__KDFNONE__SIGNONE,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__256, @Digests.HMAC_ALGORITHM.create_HmacNOSHA(), @STL.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__192__GCM__IV12__TAG16__KDFNONE__SIGNONE,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__192, @Digests.HMAC_ALGORITHM.create_HmacNOSHA(), @STL.Option<Signature.ECDSAParams>.create_None())), new Dafny.Pair<ushort,_25_AlgorithmSuite_Compile.AlgSuite>(_25_AlgorithmSuite_Compile.__default.AES__128__GCM__IV12__TAG16__KDFNONE__SIGNONE,@_25_AlgorithmSuite_Compile.AlgSuite.create(EncryptionSuites.__default.AES__GCM__128, @Digests.HMAC_ALGORITHM.create_HmacNOSHA(), @STL.Option<Signature.ECDSAParams>.create_None())));
    } }
  }
} // end of namespace _25_AlgorithmSuite_Compile
namespace Materials {






  public class EncryptedDataKey {
    public readonly Dafny.Sequence<byte> providerID;
public readonly Dafny.Sequence<byte> providerInfo;
public readonly Dafny.Sequence<byte> ciphertext;
public EncryptedDataKey(Dafny.Sequence<byte> providerID, Dafny.Sequence<byte> providerInfo, Dafny.Sequence<byte> ciphertext) {
      this.providerID = providerID;
this.providerInfo = providerInfo;
this.ciphertext = ciphertext;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.EncryptedDataKey;
return oth != null && object.Equals(this.providerID, oth.providerID) && object.Equals(this.providerInfo, oth.providerInfo) && object.Equals(this.ciphertext, oth.ciphertext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.providerID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.providerInfo));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertext));
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.EncryptedDataKey.EncryptedDataKey";
s += "(";
s += Dafny.Helpers.ToString(this.providerID);
s += ", ";
s += Dafny.Helpers.ToString(this.providerInfo);
s += ", ";
s += Dafny.Helpers.ToString(this.ciphertext);
s += ")";
return s;
    }
    static EncryptedDataKey theDefault;
public static EncryptedDataKey Default {
      get {
        if (theDefault == null) {
          theDefault = new Materials.EncryptedDataKey(UTF8.ValidUTF8Bytes.Witness, Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
        }
        return theDefault;
      }
    }
    public static EncryptedDataKey _DafnyDefaultValue() { return Default; }
public static EncryptedDataKey create(Dafny.Sequence<byte> providerID, Dafny.Sequence<byte> providerInfo, Dafny.Sequence<byte> ciphertext) {
      return new EncryptedDataKey(providerID, providerInfo, ciphertext);
    }
    public bool is_EncryptedDataKey { get { return true; } }
public Dafny.Sequence<byte> dtor_providerID {
      get {
        return this.providerID;
      }
    }
    public Dafny.Sequence<byte> dtor_providerInfo {
      get {
        return this.providerInfo;
      }
    }
    public Dafny.Sequence<byte> dtor_ciphertext {
      get {
        return this.ciphertext;
      }
    }
    public static Materials.EncryptedDataKey ValidWitness() {
      return @Materials.EncryptedDataKey.create(Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements());
    }
  }

  public partial class ValidEncryptedDataKey {
    public static readonly Materials.EncryptedDataKey Witness = Materials.EncryptedDataKey.ValidWitness();
  }

  public abstract class KeyringTraceFlag {
    public KeyringTraceFlag() { }
static KeyringTraceFlag theDefault;
public static KeyringTraceFlag Default {
      get {
        if (theDefault == null) {
          theDefault = new Materials.KeyringTraceFlag_GENERATED__DATA__KEY();
        }
        return theDefault;
      }
    }
    public static KeyringTraceFlag _DafnyDefaultValue() { return Default; }
public static KeyringTraceFlag create_GENERATED__DATA__KEY() {
      return new KeyringTraceFlag_GENERATED__DATA__KEY();
    }
    public static KeyringTraceFlag create_ENCRYPTED__DATA__KEY() {
      return new KeyringTraceFlag_ENCRYPTED__DATA__KEY();
    }
    public static KeyringTraceFlag create_DECRYPTED__DATA__KEY() {
      return new KeyringTraceFlag_DECRYPTED__DATA__KEY();
    }
    public static KeyringTraceFlag create_SIGNED__ENCRYPTION__CONTEXT() {
      return new KeyringTraceFlag_SIGNED__ENCRYPTION__CONTEXT();
    }
    public static KeyringTraceFlag create_VERIFIED__ENCRYPTION__CONTEXT() {
      return new KeyringTraceFlag_VERIFIED__ENCRYPTION__CONTEXT();
    }
    public bool is_GENERATED__DATA__KEY { get { return this is KeyringTraceFlag_GENERATED__DATA__KEY; } }
public bool is_ENCRYPTED__DATA__KEY { get { return this is KeyringTraceFlag_ENCRYPTED__DATA__KEY; } }
public bool is_DECRYPTED__DATA__KEY { get { return this is KeyringTraceFlag_DECRYPTED__DATA__KEY; } }
public bool is_SIGNED__ENCRYPTION__CONTEXT { get { return this is KeyringTraceFlag_SIGNED__ENCRYPTION__CONTEXT; } }
public bool is_VERIFIED__ENCRYPTION__CONTEXT { get { return this is KeyringTraceFlag_VERIFIED__ENCRYPTION__CONTEXT; } }
public static System.Collections.Generic.IEnumerable<KeyringTraceFlag> AllSingletonConstructors {
      get {
        yield return KeyringTraceFlag.create_GENERATED__DATA__KEY();
yield return KeyringTraceFlag.create_ENCRYPTED__DATA__KEY();
yield return KeyringTraceFlag.create_DECRYPTED__DATA__KEY();
yield return KeyringTraceFlag.create_SIGNED__ENCRYPTION__CONTEXT();
yield return KeyringTraceFlag.create_VERIFIED__ENCRYPTION__CONTEXT();
      }
    }
  }
  public class KeyringTraceFlag_GENERATED__DATA__KEY : KeyringTraceFlag {
    public KeyringTraceFlag_GENERATED__DATA__KEY() {
    }
    public override bool Equals(object other) {
      var oth = other as Materials.KeyringTraceFlag_GENERATED__DATA__KEY;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.KeyringTraceFlag.GENERATED_DATA_KEY";
return s;
    }
  }
  public class KeyringTraceFlag_ENCRYPTED__DATA__KEY : KeyringTraceFlag {
    public KeyringTraceFlag_ENCRYPTED__DATA__KEY() {
    }
    public override bool Equals(object other) {
      var oth = other as Materials.KeyringTraceFlag_ENCRYPTED__DATA__KEY;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.KeyringTraceFlag.ENCRYPTED_DATA_KEY";
return s;
    }
  }
  public class KeyringTraceFlag_DECRYPTED__DATA__KEY : KeyringTraceFlag {
    public KeyringTraceFlag_DECRYPTED__DATA__KEY() {
    }
    public override bool Equals(object other) {
      var oth = other as Materials.KeyringTraceFlag_DECRYPTED__DATA__KEY;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 2;
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.KeyringTraceFlag.DECRYPTED_DATA_KEY";
return s;
    }
  }
  public class KeyringTraceFlag_SIGNED__ENCRYPTION__CONTEXT : KeyringTraceFlag {
    public KeyringTraceFlag_SIGNED__ENCRYPTION__CONTEXT() {
    }
    public override bool Equals(object other) {
      var oth = other as Materials.KeyringTraceFlag_SIGNED__ENCRYPTION__CONTEXT;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 3;
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.KeyringTraceFlag.SIGNED_ENCRYPTION_CONTEXT";
return s;
    }
  }
  public class KeyringTraceFlag_VERIFIED__ENCRYPTION__CONTEXT : KeyringTraceFlag {
    public KeyringTraceFlag_VERIFIED__ENCRYPTION__CONTEXT() {
    }
    public override bool Equals(object other) {
      var oth = other as Materials.KeyringTraceFlag_VERIFIED__ENCRYPTION__CONTEXT;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 4;
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.KeyringTraceFlag.VERIFIED_ENCRYPTION_CONTEXT";
return s;
    }
  }

  public class KeyringTraceEntry {
    public readonly Dafny.Sequence<byte> keyNamespace;
public readonly Dafny.Sequence<byte> keyName;
public readonly Dafny.Set<Materials.KeyringTraceFlag> flags;
public KeyringTraceEntry(Dafny.Sequence<byte> keyNamespace, Dafny.Sequence<byte> keyName, Dafny.Set<Materials.KeyringTraceFlag> flags) {
      this.keyNamespace = keyNamespace;
this.keyName = keyName;
this.flags = flags;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.KeyringTraceEntry;
return oth != null && object.Equals(this.keyNamespace, oth.keyNamespace) && object.Equals(this.keyName, oth.keyName) && object.Equals(this.flags, oth.flags);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyNamespace));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyName));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.flags));
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.KeyringTraceEntry.KeyringTraceEntry";
s += "(";
s += Dafny.Helpers.ToString(this.keyNamespace);
s += ", ";
s += Dafny.Helpers.ToString(this.keyName);
s += ", ";
s += Dafny.Helpers.ToString(this.flags);
s += ")";
return s;
    }
    static KeyringTraceEntry theDefault;
public static KeyringTraceEntry Default {
      get {
        if (theDefault == null) {
          theDefault = new Materials.KeyringTraceEntry(UTF8.ValidUTF8Bytes.Witness, UTF8.ValidUTF8Bytes.Witness, Dafny.Set<Materials.KeyringTraceFlag>.Empty);
        }
        return theDefault;
      }
    }
    public static KeyringTraceEntry _DafnyDefaultValue() { return Default; }
public static KeyringTraceEntry create(Dafny.Sequence<byte> keyNamespace, Dafny.Sequence<byte> keyName, Dafny.Set<Materials.KeyringTraceFlag> flags) {
      return new KeyringTraceEntry(keyNamespace, keyName, flags);
    }
    public bool is_KeyringTraceEntry { get { return true; } }
public Dafny.Sequence<byte> dtor_keyNamespace {
      get {
        return this.keyNamespace;
      }
    }
    public Dafny.Sequence<byte> dtor_keyName {
      get {
        return this.keyName;
      }
    }
    public Dafny.Set<Materials.KeyringTraceFlag> dtor_flags {
      get {
        return this.flags;
      }
    }
  }

  public class DataKeyMaterials {
    public readonly ushort algorithmSuiteID;
public readonly Dafny.Sequence<byte> plaintextDataKey;
public readonly Dafny.Sequence<Materials.EncryptedDataKey> encryptedDataKeys;
public readonly Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace;
public DataKeyMaterials(ushort algorithmSuiteID, Dafny.Sequence<byte> plaintextDataKey, Dafny.Sequence<Materials.EncryptedDataKey> encryptedDataKeys, Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace) {
      this.algorithmSuiteID = algorithmSuiteID;
this.plaintextDataKey = plaintextDataKey;
this.encryptedDataKeys = encryptedDataKeys;
this.keyringTrace = keyringTrace;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.DataKeyMaterials;
return oth != null && this.algorithmSuiteID == oth.algorithmSuiteID && object.Equals(this.plaintextDataKey, oth.plaintextDataKey) && object.Equals(this.encryptedDataKeys, oth.encryptedDataKeys) && object.Equals(this.keyringTrace, oth.keyringTrace);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextDataKey));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptedDataKeys));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyringTrace));
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.DataKeyMaterials.DataKeyMaterials";
s += "(";
s += Dafny.Helpers.ToString(this.algorithmSuiteID);
s += ", ";
s += Dafny.Helpers.ToString(this.plaintextDataKey);
s += ", ";
s += Dafny.Helpers.ToString(this.encryptedDataKeys);
s += ", ";
s += Dafny.Helpers.ToString(this.keyringTrace);
s += ")";
return s;
    }
    static DataKeyMaterials theDefault;
public static DataKeyMaterials Default {
      get {
        if (theDefault == null) {
          theDefault = new Materials.DataKeyMaterials(_25_AlgorithmSuite_Compile.ID.Witness, Dafny.Sequence<byte>.Empty, Dafny.Sequence<Materials.EncryptedDataKey>.Empty, Dafny.Sequence<Materials.KeyringTraceEntry>.Empty);
        }
        return theDefault;
      }
    }
    public static DataKeyMaterials _DafnyDefaultValue() { return Default; }
public static DataKeyMaterials create(ushort algorithmSuiteID, Dafny.Sequence<byte> plaintextDataKey, Dafny.Sequence<Materials.EncryptedDataKey> encryptedDataKeys, Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace) {
      return new DataKeyMaterials(algorithmSuiteID, plaintextDataKey, encryptedDataKeys, keyringTrace);
    }
    public bool is_DataKeyMaterials { get { return true; } }
public ushort dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Dafny.Sequence<byte> dtor_plaintextDataKey {
      get {
        return this.plaintextDataKey;
      }
    }
    public Dafny.Sequence<Materials.EncryptedDataKey> dtor_encryptedDataKeys {
      get {
        return this.encryptedDataKeys;
      }
    }
    public Dafny.Sequence<Materials.KeyringTraceEntry> dtor_keyringTrace {
      get {
        return this.keyringTrace;
      }
    }
    public bool Valid() {
      Dafny.Sequence<Materials.KeyringTraceEntry> _587_generateTraces = STL.__default.Filter<Materials.KeyringTraceEntry>((this).dtor_keyringTrace, Materials.__default.IsGenerateTraceEntry);
Dafny.Sequence<Materials.KeyringTraceEntry> _588_encryptTraces = STL.__default.Filter<Materials.KeyringTraceEntry>((this).dtor_keyringTrace, Materials.__default.IsEncryptTraceEntry);
return (((((_25_AlgorithmSuite_Compile.ID.ValidPlaintextDataKey((this).dtor_algorithmSuiteID, (this).dtor_plaintextDataKey)) && (Dafny.Helpers.Quantifier<Materials.KeyringTraceEntry>(((this).dtor_keyringTrace).UniqueElements, true, (((_589_entry) => {
        return !(((this).dtor_keyringTrace).Contains((_589_entry))) || (((_589_entry).dtor_flags).IsSubsetOf((Materials.__default.ValidEncryptionMaterialFlags)));
      }))))) && (Dafny.Helpers.Quantifier<Materials.KeyringTraceEntry>(((this).dtor_keyringTrace).UniqueElements, true, (((_590_entry) => {
        return !(((this).dtor_keyringTrace).Contains((_590_entry))) || ((Materials.__default.IsGenerateTraceEntry(_590_entry)) || (Materials.__default.IsEncryptTraceEntry(_590_entry)));
      }))))) && ((new BigInteger((_587_generateTraces).Count)) <= (BigInteger.One))) && (!((new BigInteger((_587_generateTraces).Count)) == (BigInteger.One)) || ((((this).dtor_keyringTrace).Select(BigInteger.Zero)).Equals(((_587_generateTraces).Select(BigInteger.Zero)))))) && ((new BigInteger((_588_encryptTraces).Count)) == (new BigInteger(((this).dtor_encryptedDataKeys).Count)));
    }
    public static Materials.DataKeyMaterials ValidWitness() {
      return @Materials.DataKeyMaterials.create(_25_AlgorithmSuite_Compile.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384, ((System.Func<Dafny.Sequence<byte>>) (() => {
  BigInteger dim0 = new BigInteger(32);
var arr0 = new byte[(int)(dim0)];
for (int i0 = 0; i0 < dim0; i0++) { 
    var _591_i = (BigInteger) i0;
arr0[(int)(_591_i)] = 0;
  }
  return Dafny.Sequence<byte>.FromArray(arr0);
}))(), Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(Materials.EncryptedDataKey.ValidWitness()), Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(@Materials.KeyringTraceEntry.create(Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements(), Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_ENCRYPTED__DATA__KEY(), @Materials.KeyringTraceFlag.create_GENERATED__DATA__KEY()))));
    }
  }

  public partial class ValidDataKeyMaterials {
    public static readonly Materials.DataKeyMaterials Witness = Materials.DataKeyMaterials.ValidWitness();
  }

  public class OnDecryptResult {
    public readonly ushort algorithmSuiteID;
public readonly Dafny.Sequence<byte> plaintextDataKey;
public readonly Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace;
public OnDecryptResult(ushort algorithmSuiteID, Dafny.Sequence<byte> plaintextDataKey, Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace) {
      this.algorithmSuiteID = algorithmSuiteID;
this.plaintextDataKey = plaintextDataKey;
this.keyringTrace = keyringTrace;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.OnDecryptResult;
return oth != null && this.algorithmSuiteID == oth.algorithmSuiteID && object.Equals(this.plaintextDataKey, oth.plaintextDataKey) && object.Equals(this.keyringTrace, oth.keyringTrace);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextDataKey));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyringTrace));
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.OnDecryptResult.OnDecryptResult";
s += "(";
s += Dafny.Helpers.ToString(this.algorithmSuiteID);
s += ", ";
s += Dafny.Helpers.ToString(this.plaintextDataKey);
s += ", ";
s += Dafny.Helpers.ToString(this.keyringTrace);
s += ")";
return s;
    }
    static OnDecryptResult theDefault;
public static OnDecryptResult Default {
      get {
        if (theDefault == null) {
          theDefault = new Materials.OnDecryptResult(_25_AlgorithmSuite_Compile.ID.Witness, Dafny.Sequence<byte>.Empty, Dafny.Sequence<Materials.KeyringTraceEntry>.Empty);
        }
        return theDefault;
      }
    }
    public static OnDecryptResult _DafnyDefaultValue() { return Default; }
public static OnDecryptResult create(ushort algorithmSuiteID, Dafny.Sequence<byte> plaintextDataKey, Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace) {
      return new OnDecryptResult(algorithmSuiteID, plaintextDataKey, keyringTrace);
    }
    public bool is_OnDecryptResult { get { return true; } }
public ushort dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Dafny.Sequence<byte> dtor_plaintextDataKey {
      get {
        return this.plaintextDataKey;
      }
    }
    public Dafny.Sequence<Materials.KeyringTraceEntry> dtor_keyringTrace {
      get {
        return this.keyringTrace;
      }
    }
    public static Materials.OnDecryptResult ValidWitness() {
      Dafny.Sequence<byte> _592_pdk = ((System.Func<Dafny.Sequence<byte>>) (() => {
        BigInteger dim1 = new BigInteger(32);
var arr1 = new byte[(int)(dim1)];
for (int i1 = 0; i1 < dim1; i1++) { 
          var _593_i = (BigInteger) i1;
arr1[(int)(_593_i)] = 0;
        }
        return Dafny.Sequence<byte>.FromArray(arr1);
      }))();
Materials.KeyringTraceEntry _594_entry = @Materials.KeyringTraceEntry.create(Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements(), Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_DECRYPTED__DATA__KEY()));
Materials.OnDecryptResult _595_r = @Materials.OnDecryptResult.create(_25_AlgorithmSuite_Compile.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384, _592_pdk, Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_594_entry));
return _595_r;
    }
  }

  public partial class ValidOnDecryptResult {
    public static readonly Materials.OnDecryptResult Witness = Materials.OnDecryptResult.ValidWitness();
  }

  public class EncryptionMaterials {
    public readonly Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext;
public readonly Materials.DataKeyMaterials dataKeyMaterials;
public readonly STL.Option<Dafny.Sequence<byte>> signingKey;
public EncryptionMaterials(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Materials.DataKeyMaterials dataKeyMaterials, STL.Option<Dafny.Sequence<byte>> signingKey) {
      this.encryptionContext = encryptionContext;
this.dataKeyMaterials = dataKeyMaterials;
this.signingKey = signingKey;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.EncryptionMaterials;
return oth != null && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.dataKeyMaterials, oth.dataKeyMaterials) && object.Equals(this.signingKey, oth.signingKey);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.dataKeyMaterials));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.signingKey));
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.EncryptionMaterials.EncryptionMaterials";
s += "(";
s += Dafny.Helpers.ToString(this.encryptionContext);
s += ", ";
s += Dafny.Helpers.ToString(this.dataKeyMaterials);
s += ", ";
s += Dafny.Helpers.ToString(this.signingKey);
s += ")";
return s;
    }
    static EncryptionMaterials theDefault;
public static EncryptionMaterials Default {
      get {
        if (theDefault == null) {
          theDefault = new Materials.EncryptionMaterials(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.Empty, Materials.ValidDataKeyMaterials.Witness, STL.Option<Dafny.Sequence<byte>>.Default);
        }
        return theDefault;
      }
    }
    public static EncryptionMaterials _DafnyDefaultValue() { return Default; }
public static EncryptionMaterials create(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Materials.DataKeyMaterials dataKeyMaterials, STL.Option<Dafny.Sequence<byte>> signingKey) {
      return new EncryptionMaterials(encryptionContext, dataKeyMaterials, signingKey);
    }
    public bool is_EncryptionMaterials { get { return true; } }
public Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Materials.DataKeyMaterials dtor_dataKeyMaterials {
      get {
        return this.dataKeyMaterials;
      }
    }
    public STL.Option<Dafny.Sequence<byte>> dtor_signingKey {
      get {
        return this.signingKey;
      }
    }
    public bool Valid() {
      return !((true) && ((_25_AlgorithmSuite_Compile.ID.SignatureType(((this).dtor_dataKeyMaterials).dtor_algorithmSuiteID)).is_Some)) || ((((this).dtor_signingKey).is_Some) && ((new BigInteger((((this).dtor_dataKeyMaterials).dtor_encryptedDataKeys).Count)).Sign == 1));
    }
    public static Materials.EncryptionMaterials ValidWitness() {
      return @Materials.EncryptionMaterials.create(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements(), Materials.DataKeyMaterials.ValidWitness(), @STL.Option<Dafny.Sequence<byte>>.create_Some(((System.Func<Dafny.Sequence<byte>>) (() => {
  BigInteger dim2 = new BigInteger(32);
var arr2 = new byte[(int)(dim2)];
for (int i2 = 0; i2 < dim2; i2++) { 
    var _596_i = (BigInteger) i2;
arr2[(int)(_596_i)] = 0;
  }
  return Dafny.Sequence<byte>.FromArray(arr2);
}))()));
    }
  }

  public partial class ValidEncryptionMaterials {
    public static readonly Materials.EncryptionMaterials Witness = Materials.EncryptionMaterials.ValidWitness();
  }

  public class DecryptionMaterials {
    public readonly ushort algorithmSuiteID;
public readonly Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext;
public readonly Dafny.Sequence<byte> plaintextDataKey;
public readonly STL.Option<Dafny.Sequence<byte>> verificationKey;
public readonly Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace;
public DecryptionMaterials(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<byte> plaintextDataKey, STL.Option<Dafny.Sequence<byte>> verificationKey, Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace) {
      this.algorithmSuiteID = algorithmSuiteID;
this.encryptionContext = encryptionContext;
this.plaintextDataKey = plaintextDataKey;
this.verificationKey = verificationKey;
this.keyringTrace = keyringTrace;
    }
    public override bool Equals(object other) {
      var oth = other as Materials.DecryptionMaterials;
return oth != null && this.algorithmSuiteID == oth.algorithmSuiteID && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.plaintextDataKey, oth.plaintextDataKey) && object.Equals(this.verificationKey, oth.verificationKey) && object.Equals(this.keyringTrace, oth.keyringTrace);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintextDataKey));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.verificationKey));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyringTrace));
return (int) hash;
    }
    public override string ToString() {
      string s = "Materials_Compile.DecryptionMaterials.DecryptionMaterials";
s += "(";
s += Dafny.Helpers.ToString(this.algorithmSuiteID);
s += ", ";
s += Dafny.Helpers.ToString(this.encryptionContext);
s += ", ";
s += Dafny.Helpers.ToString(this.plaintextDataKey);
s += ", ";
s += Dafny.Helpers.ToString(this.verificationKey);
s += ", ";
s += Dafny.Helpers.ToString(this.keyringTrace);
s += ")";
return s;
    }
    static DecryptionMaterials theDefault;
public static DecryptionMaterials Default {
      get {
        if (theDefault == null) {
          theDefault = new Materials.DecryptionMaterials(_25_AlgorithmSuite_Compile.ID.Witness, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.Empty, Dafny.Sequence<byte>.Empty, STL.Option<Dafny.Sequence<byte>>.Default, Dafny.Sequence<Materials.KeyringTraceEntry>.Empty);
        }
        return theDefault;
      }
    }
    public static DecryptionMaterials _DafnyDefaultValue() { return Default; }
public static DecryptionMaterials create(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<byte> plaintextDataKey, STL.Option<Dafny.Sequence<byte>> verificationKey, Dafny.Sequence<Materials.KeyringTraceEntry> keyringTrace) {
      return new DecryptionMaterials(algorithmSuiteID, encryptionContext, plaintextDataKey, verificationKey, keyringTrace);
    }
    public bool is_DecryptionMaterials { get { return true; } }
public ushort dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.Sequence<byte> dtor_plaintextDataKey {
      get {
        return this.plaintextDataKey;
      }
    }
    public STL.Option<Dafny.Sequence<byte>> dtor_verificationKey {
      get {
        return this.verificationKey;
      }
    }
    public Dafny.Sequence<Materials.KeyringTraceEntry> dtor_keyringTrace {
      get {
        return this.keyringTrace;
      }
    }
    public bool Valid() {
      return !((_25_AlgorithmSuite_Compile.ID.ValidPlaintextDataKey((this).dtor_algorithmSuiteID, (this).dtor_plaintextDataKey)) && ((_25_AlgorithmSuite_Compile.ID.SignatureType((this).dtor_algorithmSuiteID)).is_Some)) || ((((this).dtor_verificationKey).is_Some) && (Dafny.Helpers.Quantifier<Materials.KeyringTraceEntry>(((this).dtor_keyringTrace).UniqueElements, true, (((_597_entry) => {
        return !(((this).dtor_keyringTrace).Contains((_597_entry))) || (((_597_entry).dtor_flags).IsSubsetOf((Materials.__default.ValidDecryptionMaterialFlags)));
      })))));
    }
    public static Materials.DecryptionMaterials ValidWitness() {
      return @Materials.DecryptionMaterials.create(_25_AlgorithmSuite_Compile.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements(), ((System.Func<Dafny.Sequence<byte>>) (() => {
  BigInteger dim3 = new BigInteger(32);
var arr3 = new byte[(int)(dim3)];
for (int i3 = 0; i3 < dim3; i3++) { 
    var _598_i = (BigInteger) i3;
arr3[(int)(_598_i)] = 0;
  }
  return Dafny.Sequence<byte>.FromArray(arr3);
}))(), @STL.Option<Dafny.Sequence<byte>>.create_Some(((System.Func<Dafny.Sequence<byte>>) (() => {
  BigInteger dim4 = new BigInteger(32);
var arr4 = new byte[(int)(dim4)];
for (int i4 = 0; i4 < dim4; i4++) { 
    var _599_i = (BigInteger) i4;
arr4[(int)(_599_i)] = 0;
  }
  return Dafny.Sequence<byte>.FromArray(arr4);
}))()), Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(@Materials.KeyringTraceEntry.create(Dafny.Sequence<byte>.FromElements(), Dafny.Sequence<byte>.FromElements(), Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_DECRYPTED__DATA__KEY()))));
    }
  }

  public partial class ValidDecryptionMaterials {
    public static readonly Materials.DecryptionMaterials Witness = Materials.DecryptionMaterials.ValidWitness();
  }

  public partial class __default {
    public static Dafny.Set<Dafny.Sequence<byte>> GetKeysFromEncryptionContext(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext) {
      return ((System.Func<Dafny.Set<Dafny.Sequence<byte>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Sequence<byte>>();
foreach (var _compr_0 in Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((encryptionContext).Count))) { BigInteger _600_i = (BigInteger)_compr_0;
          if (((_600_i).Sign != -1) && ((_600_i) < (new BigInteger((encryptionContext).Count)))) {
            _coll0.Add(((encryptionContext).Select(_600_i)).dtor__0);
          }
        }
        return Dafny.Set<Dafny.Sequence<byte>>.FromCollection(_coll0);
      }))();
    }
    public static bool IsGenerateTraceEntry(Materials.KeyringTraceEntry entry) {
      return ((entry).dtor_flags).Contains((@Materials.KeyringTraceFlag.create_GENERATED__DATA__KEY()));
    }
    public static bool IsEncryptTraceEntry(Materials.KeyringTraceEntry entry) {
      return ((entry).dtor_flags).Contains((@Materials.KeyringTraceFlag.create_ENCRYPTED__DATA__KEY()));
    }
    public static bool IsDecryptTraceEntry(Materials.KeyringTraceEntry entry) {
      return ((entry).dtor_flags).Contains((@Materials.KeyringTraceFlag.create_DECRYPTED__DATA__KEY()));
    }
    public static bool CompatibleDataKeyMaterials(Materials.DataKeyMaterials k1, Materials.DataKeyMaterials k2)
    {
      Dafny.Sequence<Materials.KeyringTraceEntry> _601_generateTraces = STL.__default.Filter<Materials.KeyringTraceEntry>(((k1).dtor_keyringTrace).Concat(((k2).dtor_keyringTrace)), Materials.__default.IsGenerateTraceEntry);
return (((((k1).dtor_algorithmSuiteID) == ((k2).dtor_algorithmSuiteID)) && (((k1).dtor_plaintextDataKey).Equals(((k2).dtor_plaintextDataKey)))) && ((new BigInteger((_601_generateTraces).Count)) <= (BigInteger.One))) && (!((new BigInteger((_601_generateTraces).Count)) == (BigInteger.One)) || (((new BigInteger(((k1).dtor_keyringTrace).Count)).Sign == 1) && (((_601_generateTraces).Select(BigInteger.Zero)).Equals((((k1).dtor_keyringTrace).Select(BigInteger.Zero))))));
    }
    public static Materials.DataKeyMaterials ConcatDataKeyMaterials(Materials.DataKeyMaterials k1, Materials.DataKeyMaterials k2)
    {
      Materials.DataKeyMaterials _602_r = @Materials.DataKeyMaterials.create((k1).dtor_algorithmSuiteID, (k1).dtor_plaintextDataKey, ((k1).dtor_encryptedDataKeys).Concat(((k2).dtor_encryptedDataKeys)), ((k1).dtor_keyringTrace).Concat(((k2).dtor_keyringTrace)));
return _602_r;
    }
    public static Dafny.Sequence<T> naive__merge<T>(Dafny.Sequence<T> x, Dafny.Sequence<T> y, Func<T,T,bool> lt)
    {
      if ((new BigInteger((x).Count)).Sign == 0) {
        return y;
      } else  {
        if ((new BigInteger((y).Count)).Sign == 0) {
          return x;
        } else  {
          if (Dafny.Helpers.Id<Func<T,T,bool>>(lt)((x).Select(BigInteger.Zero), (y).Select(BigInteger.Zero))) {
            return (Dafny.Sequence<T>.FromElements((x).Select(BigInteger.Zero))).Concat((Materials.__default.naive__merge<T>((x).Drop(BigInteger.One), y, lt)));
          } else  {
            return (Dafny.Sequence<T>.FromElements((y).Select(BigInteger.Zero))).Concat((Materials.__default.naive__merge<T>(x, (y).Drop(BigInteger.One), lt)));
          }
        }
      }
    }
    public static Dafny.Sequence<T> naive__merge__sort<T>(Dafny.Sequence<T> x, Func<T,T,bool> lt)
    {
      if ((new BigInteger((x).Count)) < (new BigInteger(2))) {
        return x;
      } else  {
        BigInteger _603_t = Dafny.Helpers.EuclideanDivision(new BigInteger((x).Count), new BigInteger(2));
return Materials.__default.naive__merge<T>(Materials.__default.naive__merge__sort<T>((x).Take(_603_t), lt), Materials.__default.naive__merge__sort<T>((x).Drop(_603_t), lt), lt);
      }
    }
    public static STL.Option<bool> memcmp__le(Dafny.Sequence<byte> a, Dafny.Sequence<byte> b, BigInteger len)
    {
      if ((len).Sign == 0) {
        return @STL.Option<bool>.create_None();
      } else  {
        if (((a).Select(BigInteger.Zero)) != ((b).Select(BigInteger.Zero))) {
          return @STL.Option<bool>.create_Some(((a).Select(BigInteger.Zero)) < ((b).Select(BigInteger.Zero)));
        } else  {
          return Materials.__default.memcmp__le((a).Drop(BigInteger.One), (b).Drop(BigInteger.One), (len) - (BigInteger.One));
        }
      }
    }
    public static bool lex__lt(Dafny.Sequence<byte> b, Dafny.Sequence<byte> a)
    {
      STL.Option<bool> _source5 = Materials.__default.memcmp__le(a, b, ((new BigInteger((a).Count)) < (new BigInteger((b).Count))) ? (new BigInteger((a).Count)) : (new BigInteger((b).Count)));
if (_source5.is_Some) {
        bool _604_b = ((STL.Option_Some<bool>)_source5).@get;
return !(_604_b);
      } else {
        return !((new BigInteger((a).Count)) <= (new BigInteger((b).Count)));
      }
    }
    public static bool lt__keys(_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>> b, _System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>> a)
    {
      return Materials.__default.lex__lt((b).dtor__0, (a).dtor__0);
    }
    public static Dafny.Sequence<byte> EncCtxFlatten(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> x) {
      if ((x).Equals((Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements()))) {
        return Dafny.Sequence<byte>.FromElements();
      } else  {
        return ((((x).Select(BigInteger.Zero)).dtor__0).Concat((((x).Select(BigInteger.Zero)).dtor__1))).Concat((Materials.__default.EncCtxFlatten((x).Drop(BigInteger.One))));
      }
    }
    public static Dafny.Sequence<byte> FlattenSortEncCtx(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> x) {
      return Materials.__default.EncCtxFlatten(Materials.__default.naive__merge__sort<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>(x, Materials.__default.lt__keys));
    }
    public static STL.Option<Dafny.Sequence<byte>> EncCtxLookup(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> x, Dafny.Sequence<byte> k)
    {
      if ((new BigInteger((x).Count)).Sign == 0) {
        return @STL.Option<Dafny.Sequence<byte>>.create_None();
      } else  {
        if ((((x).Select(BigInteger.Zero)).dtor__0).Equals((k))) {
          return @STL.Option<Dafny.Sequence<byte>>.create_Some(((x).Select(BigInteger.Zero)).dtor__1);
        } else  {
          return Materials.__default.EncCtxLookup((x).Drop(BigInteger.One), k);
        }
      }
    }
    public static Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> EncCtxOfStrings(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> x) {
      if ((x).Equals((Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements()))) {
        return Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements();
      } else  {
        return (Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements(@_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>.create(((x).Select(BigInteger.Zero)).dtor__0, ((x).Select(BigInteger.Zero)).dtor__1))).Concat((Materials.__default.EncCtxOfStrings((x).Drop(BigInteger.One))));
      }
    }
    public static Dafny.Set<Materials.KeyringTraceFlag> ValidEncryptionMaterialFlags { get {
      return Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_ENCRYPTED__DATA__KEY(), @Materials.KeyringTraceFlag.create_SIGNED__ENCRYPTION__CONTEXT(), @Materials.KeyringTraceFlag.create_GENERATED__DATA__KEY());
    } }
    public static Dafny.Set<Materials.KeyringTraceFlag> ValidDecryptionMaterialFlags { get {
      return Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_DECRYPTED__DATA__KEY(), @Materials.KeyringTraceFlag.create_VERIFIED__ENCRYPTION__CONTEXT());
    } }
    public static Dafny.Sequence<byte> EC__PUBLIC__KEY__FIELD { get {
      return (UTF8.__default.Encode(Dafny.Sequence<char>.FromString("aws-crypto-public-key"))).dtor_value;
    } }
  }
} // end of namespace Materials
namespace _36_KeyringDefs_Compile {





  public interface Keyring {
    STL.Result<STL.Option<Materials.DataKeyMaterials>> OnEncrypt(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, STL.Option<Dafny.Sequence<byte>> plaintextDataKey);
STL.Result<STL.Option<Materials.OnDecryptResult>> OnDecrypt(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Materials.EncryptedDataKey> edks);
  }
  public class _Companion_Keyring {
  }

} // end of namespace _36_KeyringDefs_Compile
namespace KMSUtils {





  public partial class CustomerMasterKey {
    public static readonly Dafny.Sequence<char> Witness = Dafny.Sequence<char>.FromString("alias/ExampleAlias");
  }

  public partial class GrantToken {
    public static readonly Dafny.Sequence<char> Witness = Dafny.Sequence<char>.FromString("witness");
  }

  public interface ClientSupplier {
    STL.Result<KMSUtils.KMSClient> GetClient(STL.Option<Dafny.Sequence<char>> region);
  }
  public class _Companion_ClientSupplier {
  }

  public partial class DefaultClientSupplier : KMSUtils.ClientSupplier {
    public void __ctor()
    {
      var _this = this;
    TAIL_CALL_START: ;
    }
  }

  public class ResponseMetadata {
    public readonly Dafny.Map<Dafny.Sequence<char>,Dafny.Sequence<char>> metadata;
public readonly Dafny.Sequence<char> requestID;
public ResponseMetadata(Dafny.Map<Dafny.Sequence<char>,Dafny.Sequence<char>> metadata, Dafny.Sequence<char> requestID) {
      this.metadata = metadata;
this.requestID = requestID;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.ResponseMetadata;
return oth != null && object.Equals(this.metadata, oth.metadata) && object.Equals(this.requestID, oth.requestID);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.metadata));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.requestID));
return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.ResponseMetadata.ResponseMetadata";
s += "(";
s += Dafny.Helpers.ToString(this.metadata);
s += ", ";
s += Dafny.Helpers.ToString(this.requestID);
s += ")";
return s;
    }
    static ResponseMetadata theDefault;
public static ResponseMetadata Default {
      get {
        if (theDefault == null) {
          theDefault = new KMSUtils.ResponseMetadata(Dafny.Map<Dafny.Sequence<char>,Dafny.Sequence<char>>.Empty, Dafny.Sequence<char>.Empty);
        }
        return theDefault;
      }
    }
    public static ResponseMetadata _DafnyDefaultValue() { return Default; }
public static ResponseMetadata create(Dafny.Map<Dafny.Sequence<char>,Dafny.Sequence<char>> metadata, Dafny.Sequence<char> requestID) {
      return new ResponseMetadata(metadata, requestID);
    }
    public bool is_ResponseMetadata { get { return true; } }
public Dafny.Map<Dafny.Sequence<char>,Dafny.Sequence<char>> dtor_metadata {
      get {
        return this.metadata;
      }
    }
    public Dafny.Sequence<char> dtor_requestID {
      get {
        return this.requestID;
      }
    }
  }


  public class GenerateDataKeyRequest {
    public readonly Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext;
public readonly Dafny.Sequence<Dafny.Sequence<char>> grantTokens;
public readonly Dafny.Sequence<char> keyID;
public readonly int numberOfBytes;
public GenerateDataKeyRequest(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Dafny.Sequence<char>> grantTokens, Dafny.Sequence<char> keyID, int numberOfBytes) {
      this.encryptionContext = encryptionContext;
this.grantTokens = grantTokens;
this.keyID = keyID;
this.numberOfBytes = numberOfBytes;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.GenerateDataKeyRequest;
return oth != null && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.grantTokens, oth.grantTokens) && object.Equals(this.keyID, oth.keyID) && this.numberOfBytes == oth.numberOfBytes;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.numberOfBytes));
return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.GenerateDataKeyRequest.GenerateDataKeyRequest";
s += "(";
s += Dafny.Helpers.ToString(this.encryptionContext);
s += ", ";
s += Dafny.Helpers.ToString(this.grantTokens);
s += ", ";
s += Dafny.Helpers.ToString(this.keyID);
s += ", ";
s += Dafny.Helpers.ToString(this.numberOfBytes);
s += ")";
return s;
    }
    static GenerateDataKeyRequest theDefault;
public static GenerateDataKeyRequest Default {
      get {
        if (theDefault == null) {
          theDefault = new KMSUtils.GenerateDataKeyRequest(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.Empty, Dafny.Sequence<Dafny.Sequence<char>>.Empty, KMSUtils.CustomerMasterKey.Witness, 0);
        }
        return theDefault;
      }
    }
    public static GenerateDataKeyRequest _DafnyDefaultValue() { return Default; }
public static GenerateDataKeyRequest create(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Dafny.Sequence<char>> grantTokens, Dafny.Sequence<char> keyID, int numberOfBytes) {
      return new GenerateDataKeyRequest(encryptionContext, grantTokens, keyID, numberOfBytes);
    }
    public bool is_GenerateDataKeyRequest { get { return true; } }
public Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.Sequence<Dafny.Sequence<char>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
    public Dafny.Sequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public int dtor_numberOfBytes {
      get {
        return this.numberOfBytes;
      }
    }
  }

  public class GenerateDataKeyResponse {
    public readonly Dafny.Sequence<byte> ciphertextBlob;
public readonly BigInteger contentLength;
public readonly BigInteger httpStatusCode;
public readonly Dafny.Sequence<char> keyID;
public readonly Dafny.Sequence<byte> plaintext;
public readonly KMSUtils.ResponseMetadata responseMetadata;
public GenerateDataKeyResponse(Dafny.Sequence<byte> ciphertextBlob, BigInteger contentLength, BigInteger httpStatusCode, Dafny.Sequence<char> keyID, Dafny.Sequence<byte> plaintext, KMSUtils.ResponseMetadata responseMetadata) {
      this.ciphertextBlob = ciphertextBlob;
this.contentLength = contentLength;
this.httpStatusCode = httpStatusCode;
this.keyID = keyID;
this.plaintext = plaintext;
this.responseMetadata = responseMetadata;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.GenerateDataKeyResponse;
return oth != null && object.Equals(this.ciphertextBlob, oth.ciphertextBlob) && this.contentLength == oth.contentLength && this.httpStatusCode == oth.httpStatusCode && object.Equals(this.keyID, oth.keyID) && object.Equals(this.plaintext, oth.plaintext) && object.Equals(this.responseMetadata, oth.responseMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertextBlob));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.contentLength));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.httpStatusCode));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.responseMetadata));
return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.GenerateDataKeyResponse.GenerateDataKeyResponse";
s += "(";
s += Dafny.Helpers.ToString(this.ciphertextBlob);
s += ", ";
s += Dafny.Helpers.ToString(this.contentLength);
s += ", ";
s += Dafny.Helpers.ToString(this.httpStatusCode);
s += ", ";
s += Dafny.Helpers.ToString(this.keyID);
s += ", ";
s += Dafny.Helpers.ToString(this.plaintext);
s += ", ";
s += Dafny.Helpers.ToString(this.responseMetadata);
s += ")";
return s;
    }
    static GenerateDataKeyResponse theDefault;
public static GenerateDataKeyResponse Default {
      get {
        if (theDefault == null) {
          theDefault = new KMSUtils.GenerateDataKeyResponse(Dafny.Sequence<byte>.Empty, BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, KMSUtils.ResponseMetadata.Default);
        }
        return theDefault;
      }
    }
    public static GenerateDataKeyResponse _DafnyDefaultValue() { return Default; }
public static GenerateDataKeyResponse create(Dafny.Sequence<byte> ciphertextBlob, BigInteger contentLength, BigInteger httpStatusCode, Dafny.Sequence<char> keyID, Dafny.Sequence<byte> plaintext, KMSUtils.ResponseMetadata responseMetadata) {
      return new GenerateDataKeyResponse(ciphertextBlob, contentLength, httpStatusCode, keyID, plaintext, responseMetadata);
    }
    public bool is_GenerateDataKeyResponse { get { return true; } }
public Dafny.Sequence<byte> dtor_ciphertextBlob {
      get {
        return this.ciphertextBlob;
      }
    }
    public BigInteger dtor_contentLength {
      get {
        return this.contentLength;
      }
    }
    public BigInteger dtor_httpStatusCode {
      get {
        return this.httpStatusCode;
      }
    }
    public Dafny.Sequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public Dafny.Sequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
    public KMSUtils.ResponseMetadata dtor_responseMetadata {
      get {
        return this.responseMetadata;
      }
    }
    public bool IsWellFormed() {
      return ((new BigInteger(((this).dtor_keyID).Count)) < (STLUInt.__default.UINT16__LIMIT)) && ((new BigInteger(((this).dtor_ciphertextBlob).Count)) < (STLUInt.__default.UINT16__LIMIT));
    }
  }

  public class EncryptRequest {
    public readonly Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext;
public readonly Dafny.Sequence<Dafny.Sequence<char>> grantTokens;
public readonly Dafny.Sequence<char> keyID;
public readonly Dafny.Sequence<byte> plaintext;
public EncryptRequest(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Dafny.Sequence<char>> grantTokens, Dafny.Sequence<char> keyID, Dafny.Sequence<byte> plaintext) {
      this.encryptionContext = encryptionContext;
this.grantTokens = grantTokens;
this.keyID = keyID;
this.plaintext = plaintext;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.EncryptRequest;
return oth != null && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.grantTokens, oth.grantTokens) && object.Equals(this.keyID, oth.keyID) && object.Equals(this.plaintext, oth.plaintext);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.EncryptRequest.EncryptRequest";
s += "(";
s += Dafny.Helpers.ToString(this.encryptionContext);
s += ", ";
s += Dafny.Helpers.ToString(this.grantTokens);
s += ", ";
s += Dafny.Helpers.ToString(this.keyID);
s += ", ";
s += Dafny.Helpers.ToString(this.plaintext);
s += ")";
return s;
    }
    static EncryptRequest theDefault;
public static EncryptRequest Default {
      get {
        if (theDefault == null) {
          theDefault = new KMSUtils.EncryptRequest(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.Empty, Dafny.Sequence<Dafny.Sequence<char>>.Empty, KMSUtils.CustomerMasterKey.Witness, Dafny.Sequence<byte>.Empty);
        }
        return theDefault;
      }
    }
    public static EncryptRequest _DafnyDefaultValue() { return Default; }
public static EncryptRequest create(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Dafny.Sequence<char>> grantTokens, Dafny.Sequence<char> keyID, Dafny.Sequence<byte> plaintext) {
      return new EncryptRequest(encryptionContext, grantTokens, keyID, plaintext);
    }
    public bool is_EncryptRequest { get { return true; } }
public Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.Sequence<Dafny.Sequence<char>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
    public Dafny.Sequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public Dafny.Sequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
  }

  public class EncryptResponse {
    public readonly Dafny.Sequence<byte> ciphertextBlob;
public readonly BigInteger contentLength;
public readonly BigInteger httpStatusCode;
public readonly Dafny.Sequence<char> keyID;
public readonly KMSUtils.ResponseMetadata responseMetadata;
public EncryptResponse(Dafny.Sequence<byte> ciphertextBlob, BigInteger contentLength, BigInteger httpStatusCode, Dafny.Sequence<char> keyID, KMSUtils.ResponseMetadata responseMetadata) {
      this.ciphertextBlob = ciphertextBlob;
this.contentLength = contentLength;
this.httpStatusCode = httpStatusCode;
this.keyID = keyID;
this.responseMetadata = responseMetadata;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.EncryptResponse;
return oth != null && object.Equals(this.ciphertextBlob, oth.ciphertextBlob) && this.contentLength == oth.contentLength && this.httpStatusCode == oth.httpStatusCode && object.Equals(this.keyID, oth.keyID) && object.Equals(this.responseMetadata, oth.responseMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertextBlob));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.contentLength));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.httpStatusCode));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.responseMetadata));
return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.EncryptResponse.EncryptResponse";
s += "(";
s += Dafny.Helpers.ToString(this.ciphertextBlob);
s += ", ";
s += Dafny.Helpers.ToString(this.contentLength);
s += ", ";
s += Dafny.Helpers.ToString(this.httpStatusCode);
s += ", ";
s += Dafny.Helpers.ToString(this.keyID);
s += ", ";
s += Dafny.Helpers.ToString(this.responseMetadata);
s += ")";
return s;
    }
    static EncryptResponse theDefault;
public static EncryptResponse Default {
      get {
        if (theDefault == null) {
          theDefault = new KMSUtils.EncryptResponse(Dafny.Sequence<byte>.Empty, BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<char>.Empty, KMSUtils.ResponseMetadata.Default);
        }
        return theDefault;
      }
    }
    public static EncryptResponse _DafnyDefaultValue() { return Default; }
public static EncryptResponse create(Dafny.Sequence<byte> ciphertextBlob, BigInteger contentLength, BigInteger httpStatusCode, Dafny.Sequence<char> keyID, KMSUtils.ResponseMetadata responseMetadata) {
      return new EncryptResponse(ciphertextBlob, contentLength, httpStatusCode, keyID, responseMetadata);
    }
    public bool is_EncryptResponse { get { return true; } }
public Dafny.Sequence<byte> dtor_ciphertextBlob {
      get {
        return this.ciphertextBlob;
      }
    }
    public BigInteger dtor_contentLength {
      get {
        return this.contentLength;
      }
    }
    public BigInteger dtor_httpStatusCode {
      get {
        return this.httpStatusCode;
      }
    }
    public Dafny.Sequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public KMSUtils.ResponseMetadata dtor_responseMetadata {
      get {
        return this.responseMetadata;
      }
    }
    public bool IsWellFormed() {
      return ((new BigInteger(((this).dtor_keyID).Count)) < (STLUInt.__default.UINT16__LIMIT)) && ((new BigInteger(((this).dtor_ciphertextBlob).Count)) < (STLUInt.__default.UINT16__LIMIT));
    }
  }

  public class DecryptRequest {
    public readonly Dafny.Sequence<byte> ciphertextBlob;
public readonly Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext;
public readonly Dafny.Sequence<Dafny.Sequence<char>> grantTokens;
public DecryptRequest(Dafny.Sequence<byte> ciphertextBlob, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Dafny.Sequence<char>> grantTokens) {
      this.ciphertextBlob = ciphertextBlob;
this.encryptionContext = encryptionContext;
this.grantTokens = grantTokens;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.DecryptRequest;
return oth != null && object.Equals(this.ciphertextBlob, oth.ciphertextBlob) && object.Equals(this.encryptionContext, oth.encryptionContext) && object.Equals(this.grantTokens, oth.grantTokens);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertextBlob));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionContext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.grantTokens));
return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.DecryptRequest.DecryptRequest";
s += "(";
s += Dafny.Helpers.ToString(this.ciphertextBlob);
s += ", ";
s += Dafny.Helpers.ToString(this.encryptionContext);
s += ", ";
s += Dafny.Helpers.ToString(this.grantTokens);
s += ")";
return s;
    }
    static DecryptRequest theDefault;
public static DecryptRequest Default {
      get {
        if (theDefault == null) {
          theDefault = new KMSUtils.DecryptRequest(Dafny.Sequence<byte>.Empty, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.Empty, Dafny.Sequence<Dafny.Sequence<char>>.Empty);
        }
        return theDefault;
      }
    }
    public static DecryptRequest _DafnyDefaultValue() { return Default; }
public static DecryptRequest create(Dafny.Sequence<byte> ciphertextBlob, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Dafny.Sequence<char>> grantTokens) {
      return new DecryptRequest(ciphertextBlob, encryptionContext, grantTokens);
    }
    public bool is_DecryptRequest { get { return true; } }
public Dafny.Sequence<byte> dtor_ciphertextBlob {
      get {
        return this.ciphertextBlob;
      }
    }
    public Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> dtor_encryptionContext {
      get {
        return this.encryptionContext;
      }
    }
    public Dafny.Sequence<Dafny.Sequence<char>> dtor_grantTokens {
      get {
        return this.grantTokens;
      }
    }
  }

  public class DecryptResponse {
    public readonly BigInteger contentLength;
public readonly BigInteger httpStatusCode;
public readonly Dafny.Sequence<char> keyID;
public readonly Dafny.Sequence<byte> plaintext;
public readonly KMSUtils.ResponseMetadata responseMetadata;
public DecryptResponse(BigInteger contentLength, BigInteger httpStatusCode, Dafny.Sequence<char> keyID, Dafny.Sequence<byte> plaintext, KMSUtils.ResponseMetadata responseMetadata) {
      this.contentLength = contentLength;
this.httpStatusCode = httpStatusCode;
this.keyID = keyID;
this.plaintext = plaintext;
this.responseMetadata = responseMetadata;
    }
    public override bool Equals(object other) {
      var oth = other as KMSUtils.DecryptResponse;
return oth != null && this.contentLength == oth.contentLength && this.httpStatusCode == oth.httpStatusCode && object.Equals(this.keyID, oth.keyID) && object.Equals(this.plaintext, oth.plaintext) && object.Equals(this.responseMetadata, oth.responseMetadata);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.contentLength));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.httpStatusCode));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.responseMetadata));
return (int) hash;
    }
    public override string ToString() {
      string s = "KMSUtils_Compile.DecryptResponse.DecryptResponse";
s += "(";
s += Dafny.Helpers.ToString(this.contentLength);
s += ", ";
s += Dafny.Helpers.ToString(this.httpStatusCode);
s += ", ";
s += Dafny.Helpers.ToString(this.keyID);
s += ", ";
s += Dafny.Helpers.ToString(this.plaintext);
s += ", ";
s += Dafny.Helpers.ToString(this.responseMetadata);
s += ")";
return s;
    }
    static DecryptResponse theDefault;
public static DecryptResponse Default {
      get {
        if (theDefault == null) {
          theDefault = new KMSUtils.DecryptResponse(BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<char>.Empty, Dafny.Sequence<byte>.Empty, KMSUtils.ResponseMetadata.Default);
        }
        return theDefault;
      }
    }
    public static DecryptResponse _DafnyDefaultValue() { return Default; }
public static DecryptResponse create(BigInteger contentLength, BigInteger httpStatusCode, Dafny.Sequence<char> keyID, Dafny.Sequence<byte> plaintext, KMSUtils.ResponseMetadata responseMetadata) {
      return new DecryptResponse(contentLength, httpStatusCode, keyID, plaintext, responseMetadata);
    }
    public bool is_DecryptResponse { get { return true; } }
public BigInteger dtor_contentLength {
      get {
        return this.contentLength;
      }
    }
    public BigInteger dtor_httpStatusCode {
      get {
        return this.httpStatusCode;
      }
    }
    public Dafny.Sequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public Dafny.Sequence<byte> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
    public KMSUtils.ResponseMetadata dtor_responseMetadata {
      get {
        return this.responseMetadata;
      }
    }
  }

  public partial class KMSClient {
  }

  public partial class __default {
    public static bool ValidFormatCMK(Dafny.Sequence<char> cmk) {
      return ((KMSUtils.__default.ValidFormatCMKKeyARN(cmk)) || (KMSUtils.__default.ValidFormatCMKAlias(cmk))) || (KMSUtils.__default.ValidFormatCMKAliasARN(cmk));
    }
    public static bool ValidFormatCMKKeyARN(Dafny.Sequence<char> cmk) {
      Dafny.Sequence<Dafny.Sequence<char>> _605_components = STL.__default.Split<char>(cmk, ':');
return (((((UTF8.__default.IsASCIIString(cmk)) && (((new BigInteger((cmk).Count)).Sign == 1) && ((new BigInteger((cmk).Count)) <= (new BigInteger(2048))))) && ((new BigInteger((_605_components).Count)) == (new BigInteger(6)))) && (((_605_components).Select(BigInteger.Zero)).Equals((Dafny.Sequence<char>.FromString("arn"))))) && (((_605_components).Select(new BigInteger(2))).Equals((Dafny.Sequence<char>.FromString("kms"))))) && (((STL.__default.Split<char>((_605_components).Select(new BigInteger(5)), '/')).Select(BigInteger.Zero)).Equals((Dafny.Sequence<char>.FromString("key"))));
    }
    public static bool ValidFormatCMKAlias(Dafny.Sequence<char> cmk) {
      Dafny.Sequence<Dafny.Sequence<char>> _606_components = STL.__default.Split<char>(cmk, '/');
return (((UTF8.__default.IsASCIIString(cmk)) && (((new BigInteger((cmk).Count)).Sign == 1) && ((new BigInteger((cmk).Count)) <= (new BigInteger(2048))))) && ((new BigInteger((_606_components).Count)) == (new BigInteger(2)))) && (((_606_components).Select(BigInteger.Zero)).Equals((Dafny.Sequence<char>.FromString("alias"))));
    }
    public static bool ValidFormatCMKAliasARN(Dafny.Sequence<char> cmk) {
      Dafny.Sequence<Dafny.Sequence<char>> _607_components = STL.__default.Split<char>(cmk, ':');
return (((((UTF8.__default.IsASCIIString(cmk)) && (((new BigInteger((cmk).Count)).Sign == 1) && ((new BigInteger((cmk).Count)) <= (new BigInteger(2048))))) && ((new BigInteger((_607_components).Count)) == (new BigInteger(6)))) && (((_607_components).Select(BigInteger.Zero)).Equals((Dafny.Sequence<char>.FromString("arn"))))) && (((_607_components).Select(new BigInteger(2))).Equals((Dafny.Sequence<char>.FromString("kms"))))) && (((STL.__default.Split<char>((_607_components).Select(new BigInteger(5)), '/')).Select(BigInteger.Zero)).Equals((Dafny.Sequence<char>.FromString("alias"))));
    }
    public static BigInteger MAX__GRANT__TOKENS { get {
      return new BigInteger(10);
    } }
  }
} // end of namespace KMSUtils
namespace _46_KMSKeyring_Compile {








  public partial class KMSKeyring : _36_KeyringDefs_Compile.Keyring {
    public void __ctor(KMSUtils.ClientSupplier clientSupplier, Dafny.Sequence<Dafny.Sequence<char>> keyIDs, STL.Option<Dafny.Sequence<char>> generator, Dafny.Sequence<Dafny.Sequence<char>> grantTokens)
    {
      var _this = this;
    TAIL_CALL_START: ;
      { }
      (_this)._clientSupplier = clientSupplier;
      (_this)._keyIDs = keyIDs;
      (_this)._generator = generator;
      (_this)._grantTokens = grantTokens;
      (_this)._isDiscovery = ((new BigInteger((keyIDs).Count)).Sign == 0) && ((generator).is_None);
    }
    public STL.Result<Materials.DataKeyMaterials> Generate(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext)
    {
      STL.Result<Materials.DataKeyMaterials> res = STL.Result<Materials.DataKeyMaterials>.Default;
      KMSUtils.GenerateDataKeyRequest _608_generatorRequest;
      _608_generatorRequest = @KMSUtils.GenerateDataKeyRequest.create(encryptionContext, (this).grantTokens, ((this).generator).dtor_get, (int)(_25_AlgorithmSuite_Compile.ID.KDFInputKeyLength(algorithmSuiteID)));
      STL.Result<Dafny.Sequence<char>> _609_regionRes;
      _609_regionRes = _46_KMSKeyring_Compile.__default.RegionFromKMSKeyARN(((this).generator).dtor_get);
      STL.Option<Dafny.Sequence<char>> _610_regionOpt;
      _610_regionOpt = (_609_regionRes).ToOption();
      KMSUtils.KMSClient _611_client = default(KMSUtils.KMSClient);
      STL.Result<KMSUtils.KMSClient> _612_valueOrError0;
STL.Result<KMSUtils.KMSClient> _out0;
var _outcollector0 = ((this).clientSupplier).GetClient(_610_regionOpt);
_out0 = _outcollector0;
_612_valueOrError0 = _out0;
      if ((_612_valueOrError0).IsFailure()) {
        res = (_612_valueOrError0).PropagateFailure<Materials.DataKeyMaterials>();
return res;
      }
      _611_client = (_612_valueOrError0).Extract();
      KMSUtils.GenerateDataKeyResponse _613_generatorResponse = KMSUtils.GenerateDataKeyResponse.Default;
      STL.Result<KMSUtils.GenerateDataKeyResponse> _614_valueOrError1;
STL.Result<KMSUtils.GenerateDataKeyResponse> _out1;
var _outcollector1 = (_611_client).GenerateDataKey(_608_generatorRequest);
_out1 = _outcollector1;
_614_valueOrError1 = _out1;
      if ((_614_valueOrError1).IsFailure()) {
        res = (_614_valueOrError1).PropagateFailure<Materials.DataKeyMaterials>();
return res;
      }
      _613_generatorResponse = (_614_valueOrError1).Extract();
      if (!((_613_generatorResponse).IsWellFormed())) {
        res = @STL.Result<Materials.DataKeyMaterials>.create_Failure(Dafny.Sequence<char>.FromString("Invalid response from KMS GenerateDataKey"));
return res;
      }
      Dafny.Sequence<byte> _615_providerInfo = UTF8.ValidUTF8Bytes.Witness;
      STL.Result<Dafny.Sequence<byte>> _616_valueOrError2;
      _616_valueOrError2 = UTF8.__default.Encode((_613_generatorResponse).dtor_keyID);
      if ((_616_valueOrError2).IsFailure()) {
        res = (_616_valueOrError2).PropagateFailure<Materials.DataKeyMaterials>();
return res;
      }
      _615_providerInfo = (_616_valueOrError2).Extract();
      if ((STLUInt.__default.UINT16__LIMIT) <= (new BigInteger((_615_providerInfo).Count))) {
        res = @STL.Result<Materials.DataKeyMaterials>.create_Failure(Dafny.Sequence<char>.FromString("providerInfo exceeds maximum length"));
return res;
      }
      Materials.EncryptedDataKey _617_encryptedDataKey;
      _617_encryptedDataKey = @Materials.EncryptedDataKey.create(_46_KMSKeyring_Compile.__default.PROVIDER__ID, _615_providerInfo, (_613_generatorResponse).dtor_ciphertextBlob);
      Dafny.Sequence<char> _618_keyID;
      _618_keyID = (_613_generatorResponse).dtor_keyID;
      Dafny.Sequence<byte> _619_plaintextDataKey;
      _619_plaintextDataKey = (_613_generatorResponse).dtor_plaintext;
      if (!(_25_AlgorithmSuite_Compile.ID.ValidPlaintextDataKey(algorithmSuiteID, _619_plaintextDataKey))) {
        res = @STL.Result<Materials.DataKeyMaterials>.create_Failure(Dafny.Sequence<char>.FromString("Invalid response from KMS GenerateDataKey: Invalid key"));
return res;
      }
      Materials.KeyringTraceEntry _620_generateTraceEntry;
      _620_generateTraceEntry = @Materials.KeyringTraceEntry.create(_46_KMSKeyring_Compile.__default.PROVIDER__ID, (UTF8.__default.Encode(((this).generator).dtor_get)).dtor_value, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_GENERATED__DATA__KEY(), @Materials.KeyringTraceFlag.create_ENCRYPTED__DATA__KEY(), @Materials.KeyringTraceFlag.create_SIGNED__ENCRYPTION__CONTEXT()));
      Materials.DataKeyMaterials _621_datakeyMaterials;
      _621_datakeyMaterials = @Materials.DataKeyMaterials.create(algorithmSuiteID, _619_plaintextDataKey, Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(_617_encryptedDataKey), Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_620_generateTraceEntry));
      { }
      res = @STL.Result<Materials.DataKeyMaterials>.create_Success(_621_datakeyMaterials);
return res;
      return res;
    }
    public STL.Result<STL.Option<Materials.DataKeyMaterials>> OnEncrypt(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, STL.Option<Dafny.Sequence<byte>> plaintextDataKey)
    {
      STL.Result<STL.Option<Materials.DataKeyMaterials>> res = STL.Result<STL.Option<Materials.DataKeyMaterials>>.Default;
      if ((this).isDiscovery) {
        res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Success(@STL.Option<Materials.DataKeyMaterials>.create_None());
return res;
      } else if (((plaintextDataKey).is_None) && (((this).generator).is_None)) {
        res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Failure(Dafny.Sequence<char>.FromString("No plaintext datakey or generator defined"));
return res;
      }
      Dafny.Sequence<Dafny.Sequence<char>> _622_encryptCMKs;
      _622_encryptCMKs = (this).keyIDs;
      Dafny.Sequence<Materials.EncryptedDataKey> _623_edks;
      _623_edks = Dafny.Sequence<Materials.EncryptedDataKey>.FromElements();
      Dafny.Sequence<Materials.KeyringTraceEntry> _624_keyringTrace;
      _624_keyringTrace = Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements();
      Dafny.Sequence<byte> _625_ptdk = Dafny.Sequence<byte>.Empty;
      if (((this).generator).is_Some) {
        if ((plaintextDataKey).is_None) {
          Materials.DataKeyMaterials _626_generatedMaterials = Materials.ValidDataKeyMaterials.Witness;
          STL.Result<Materials.DataKeyMaterials> _627_valueOrError0;
STL.Result<Materials.DataKeyMaterials> _out2;
var _outcollector2 = (this).Generate(algorithmSuiteID, encryptionContext);
_out2 = _outcollector2;
_627_valueOrError0 = _out2;
          if ((_627_valueOrError0).IsFailure()) {
            res = (_627_valueOrError0).PropagateFailure<STL.Option<Materials.DataKeyMaterials>>();
return res;
          }
          _626_generatedMaterials = (_627_valueOrError0).Extract();
          _625_ptdk = (_626_generatedMaterials).dtor_plaintextDataKey;
          _623_edks = (_626_generatedMaterials).dtor_encryptedDataKeys;
          _624_keyringTrace = (_626_generatedMaterials).dtor_keyringTrace;
        } else {
          _625_ptdk = (plaintextDataKey).dtor_get;
          _622_encryptCMKs = (_622_encryptCMKs).Concat((Dafny.Sequence<Dafny.Sequence<char>>.FromElements(((this).generator).dtor_get)));
        }
      } else {
        _625_ptdk = (plaintextDataKey).dtor_get;
      }
      BigInteger _628_i;
      _628_i = BigInteger.Zero;
      while ((_628_i) < (new BigInteger((_622_encryptCMKs).Count))) {
        KMSUtils.EncryptRequest _629_encryptRequest;
        _629_encryptRequest = @KMSUtils.EncryptRequest.create(encryptionContext, (this).grantTokens, (_622_encryptCMKs).Select(_628_i), _625_ptdk);
        STL.Result<Dafny.Sequence<char>> _630_regionRes;
        _630_regionRes = _46_KMSKeyring_Compile.__default.RegionFromKMSKeyARN((_622_encryptCMKs).Select(_628_i));
        STL.Option<Dafny.Sequence<char>> _631_regionOpt;
        _631_regionOpt = (_630_regionRes).ToOption();
        KMSUtils.KMSClient _632_client = default(KMSUtils.KMSClient);
        STL.Result<KMSUtils.KMSClient> _633_valueOrError1;
STL.Result<KMSUtils.KMSClient> _out3;
var _outcollector3 = ((this).clientSupplier).GetClient(_631_regionOpt);
_out3 = _outcollector3;
_633_valueOrError1 = _out3;
        if ((_633_valueOrError1).IsFailure()) {
          res = (_633_valueOrError1).PropagateFailure<STL.Option<Materials.DataKeyMaterials>>();
return res;
        }
        _632_client = (_633_valueOrError1).Extract();
        KMSUtils.EncryptResponse _634_encryptResponse = KMSUtils.EncryptResponse.Default;
        STL.Result<KMSUtils.EncryptResponse> _635_valueOrError2;
STL.Result<KMSUtils.EncryptResponse> _out4;
var _outcollector4 = (_632_client).Encrypt(_629_encryptRequest);
_out4 = _outcollector4;
_635_valueOrError2 = _out4;
        if ((_635_valueOrError2).IsFailure()) {
          res = (_635_valueOrError2).PropagateFailure<STL.Option<Materials.DataKeyMaterials>>();
return res;
        }
        _634_encryptResponse = (_635_valueOrError2).Extract();
        if ((_634_encryptResponse).IsWellFormed()) {
          Dafny.Sequence<byte> _636_providerInfo = UTF8.ValidUTF8Bytes.Witness;
          STL.Result<Dafny.Sequence<byte>> _637_valueOrError3;
          _637_valueOrError3 = UTF8.__default.Encode((_634_encryptResponse).dtor_keyID);
          if ((_637_valueOrError3).IsFailure()) {
            res = (_637_valueOrError3).PropagateFailure<STL.Option<Materials.DataKeyMaterials>>();
return res;
          }
          _636_providerInfo = (_637_valueOrError3).Extract();
          if ((STLUInt.__default.UINT16__LIMIT) <= (new BigInteger((_636_providerInfo).Count))) {
            res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Failure(Dafny.Sequence<char>.FromString("providerInfo exceeds maximum length"));
return res;
          }
          Materials.EncryptedDataKey _638_edk;
          _638_edk = @Materials.EncryptedDataKey.create(_46_KMSKeyring_Compile.__default.PROVIDER__ID, _636_providerInfo, (_634_encryptResponse).dtor_ciphertextBlob);
          Materials.KeyringTraceEntry _639_encryptTraceEntry;
          _639_encryptTraceEntry = @Materials.KeyringTraceEntry.create(_46_KMSKeyring_Compile.__default.PROVIDER__ID, (UTF8.__default.Encode((_622_encryptCMKs).Select(_628_i))).dtor_value, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_ENCRYPTED__DATA__KEY(), @Materials.KeyringTraceFlag.create_SIGNED__ENCRYPTION__CONTEXT()));
          _623_edks = (_623_edks).Concat((Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(_638_edk)));
          { }
          { }
          _624_keyringTrace = (_624_keyringTrace).Concat((Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_639_encryptTraceEntry)));
        } else {
          res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Failure(Dafny.Sequence<char>.FromString("Invalid response from KMS Encrypt"));
return res;
        }
        _628_i = (_628_i) + (BigInteger.One);
      }
      Materials.DataKeyMaterials _640_datakeyMat;
      _640_datakeyMat = @Materials.DataKeyMaterials.create(algorithmSuiteID, _625_ptdk, _623_edks, _624_keyringTrace);
      { }
      res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Success(@STL.Option<Materials.DataKeyMaterials>.create_Some(_640_datakeyMat));
return res;
      return res;
    }
    public bool ShouldAttemptDecryption(Materials.EncryptedDataKey edk) {
      Dafny.Sequence<Dafny.Sequence<char>> _641_keys = (((this).generator).is_Some) ? (((this).keyIDs).Concat((Dafny.Sequence<Dafny.Sequence<char>>.FromElements(((this).generator).dtor_get)))) : ((this).keyIDs);
return ((((((edk).dtor_providerID).Equals((_46_KMSKeyring_Compile.__default.PROVIDER__ID))) && (UTF8.__default.ValidUTF8Seq((edk).dtor_providerInfo))) && ((UTF8.__default.Decode((edk).dtor_providerInfo)).is_Success)) && (KMSUtils.__default.ValidFormatCMK((UTF8.__default.Decode((edk).dtor_providerInfo)).dtor_value))) && (((this).isDiscovery) || ((_641_keys).Contains(((UTF8.__default.Decode((edk).dtor_providerInfo)).dtor_value))));
    }
    public STL.Result<STL.Option<Materials.OnDecryptResult>> OnDecrypt(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Materials.EncryptedDataKey> edks)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<STL.Option<Materials.OnDecryptResult>> res = STL.Result<STL.Option<Materials.OnDecryptResult>>.Default;
      if ((new BigInteger((edks).Count)).Sign == 0) {
        res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Success(@STL.Option<Materials.OnDecryptResult>.create_None());
return res;
      }
      BigInteger _642_i;
      _642_i = BigInteger.Zero;
      while ((_642_i) < (new BigInteger((edks).Count))) {
        Materials.EncryptedDataKey _643_edk;
        _643_edk = (edks).Select(_642_i);
        if ((_this).ShouldAttemptDecryption(_643_edk)) {
          KMSUtils.DecryptRequest _644_decryptRequest;
          _644_decryptRequest = @KMSUtils.DecryptRequest.create((_643_edk).dtor_ciphertext, encryptionContext, (_this).grantTokens);
          Dafny.Sequence<char> _645_providerInfo;
          _645_providerInfo = (UTF8.__default.Decode((_643_edk).dtor_providerInfo)).dtor_value;
          STL.Result<Dafny.Sequence<char>> _646_regionRes;
          _646_regionRes = _46_KMSKeyring_Compile.__default.RegionFromKMSKeyARN(_645_providerInfo);
          STL.Option<Dafny.Sequence<char>> _647_regionOpt;
          _647_regionOpt = (_646_regionRes).ToOption();
          STL.Result<KMSUtils.KMSClient> _648_clientRes;
STL.Result<KMSUtils.KMSClient> _out5;
var _outcollector5 = ((_this).clientSupplier).GetClient(_647_regionOpt);
_out5 = _outcollector5;
_648_clientRes = _out5;
          if ((_648_clientRes).is_Success) {
            KMSUtils.KMSClient _649_client;
            _649_client = (_648_clientRes).dtor_value;
            STL.Result<KMSUtils.DecryptResponse> _650_decryptResponseResult;
STL.Result<KMSUtils.DecryptResponse> _out6;
var _outcollector6 = (_649_client).Decrypt(_644_decryptRequest);
_out6 = _outcollector6;
_650_decryptResponseResult = _out6;
            if ((_650_decryptResponseResult).is_Success) {
              KMSUtils.DecryptResponse _651_decryptResponse;
              _651_decryptResponse = (_650_decryptResponseResult).dtor_value;
              if ((!((_651_decryptResponse).dtor_keyID).Equals(((UTF8.__default.Decode((_643_edk).dtor_providerInfo)).dtor_value))) || (!(_25_AlgorithmSuite_Compile.ID.ValidPlaintextDataKey(algorithmSuiteID, (_651_decryptResponse).dtor_plaintext)))) {
                res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Failure(Dafny.Sequence<char>.FromString("Invalid response from KMS Decrypt"));
return res;
              } else {
                Materials.KeyringTraceEntry _652_decryptTraceEntry;
                _652_decryptTraceEntry = @Materials.KeyringTraceEntry.create(_46_KMSKeyring_Compile.__default.PROVIDER__ID, (_643_edk).dtor_providerInfo, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_DECRYPTED__DATA__KEY(), @Materials.KeyringTraceFlag.create_VERIFIED__ENCRYPTION__CONTEXT()));
                res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Success(@STL.Option<Materials.OnDecryptResult>.create_Some(@Materials.OnDecryptResult.create(algorithmSuiteID, (_651_decryptResponse).dtor_plaintext, Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_652_decryptTraceEntry))));
return res;
              }
            }
          }
        }
        _642_i = (_642_i) + (BigInteger.One);
      }
      res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Success(@STL.Option<Materials.OnDecryptResult>.create_None());
return res;
      return res;
    }
    public KMSUtils.ClientSupplier _clientSupplier = default(KMSUtils.ClientSupplier);
public KMSUtils.ClientSupplier clientSupplier { get {
      return this._clientSupplier;
    } }
    public Dafny.Sequence<Dafny.Sequence<char>> _keyIDs = Dafny.Sequence<Dafny.Sequence<char>>.Empty;
public Dafny.Sequence<Dafny.Sequence<char>> keyIDs { get {
      return this._keyIDs;
    } }
    public STL.Option<Dafny.Sequence<char>> _generator = STL.Option<Dafny.Sequence<char>>.Default;
public STL.Option<Dafny.Sequence<char>> generator { get {
      return this._generator;
    } }
    public Dafny.Sequence<Dafny.Sequence<char>> _grantTokens = Dafny.Sequence<Dafny.Sequence<char>>.Empty;
public Dafny.Sequence<Dafny.Sequence<char>> grantTokens { get {
      return this._grantTokens;
    } }
    public bool _isDiscovery = false;
public bool isDiscovery { get {
      return this._isDiscovery;
    } }
  }

  public partial class __default {
    public static STL.Result<Dafny.Sequence<char>> RegionFromKMSKeyARN(Dafny.Sequence<char> arn) {
      Dafny.Sequence<Dafny.Sequence<char>> _653_components = STL.__default.Split<char>(arn, ':');
if ((((new BigInteger(6)) <= (new BigInteger((_653_components).Count))) && (((_653_components).Select(BigInteger.Zero)).Equals((Dafny.Sequence<char>.FromString("arn"))))) && (((_653_components).Select(new BigInteger(2))).Equals((Dafny.Sequence<char>.FromString("kms"))))) {
        return @STL.Result<Dafny.Sequence<char>>.create_Success((_653_components).Select(new BigInteger(3)));
      } else  {
        return @STL.Result<Dafny.Sequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Malformed ARN"));
      }
    }
    public static Dafny.Sequence<byte> PROVIDER__ID { get {
      return (UTF8.__default.Encode(Dafny.Sequence<char>.FromString("aws-kms"))).dtor_value;
    } }
  }
} // end of namespace _46_KMSKeyring_Compile
namespace _54_Streams_Compile {



  public partial class StringReader {
    public BigInteger pos = BigInteger.Zero;
public BigInteger Available() {
      return (new BigInteger(((this).data).Length)) - (this.pos);
    }
    public void __ctor(byte[] d)
    {
      var _this = this;
    TAIL_CALL_START: ;
      { }
      (_this)._data = d;
      (_this).pos = BigInteger.Zero;
    }
    public void FromSeq(Dafny.Sequence<byte> s)
    {
      var _this = this;
    TAIL_CALL_START: ;
      byte[] _654_d;
      var _nw4 = new byte[(int)(new BigInteger((s).Count))];
var _arrayinit1 = Dafny.Helpers.Id<Func<Dafny.Sequence<byte>,Func<BigInteger,byte>>>((_655_s) => ((System.Func<BigInteger, byte>)((_656_i) => {
        return (_655_s).Select(_656_i);
      })))(s);
for (var _arrayinit_01 = 0; _arrayinit_01 < _nw4.Length; _arrayinit_01++) {
        _nw4[(int)(_arrayinit_01)] = _arrayinit1(_arrayinit_01);
      }
      _654_d = _nw4;
      { }
      (_this)._data = _654_d;
      (_this).pos = BigInteger.Zero;
    }
    public STL.Result<BigInteger> Read(byte[] arr, BigInteger off, BigInteger req)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<BigInteger> res = STL.Result<BigInteger>.Default;
      BigInteger _657_n;
      _657_n = STL.__default.min(req, (_this).Available());
      var _ingredients0 = new System.Collections.Generic.List<System.Tuple<byte[],int,byte>>();
foreach (var _658_i in Dafny.Helpers.IntegerRange(BigInteger.Zero, _657_n)) {
        if ((true) && (((_658_i).Sign != -1) && ((_658_i) < (_657_n)))) {
          _ingredients0.Add(new System.Tuple<byte[],int,byte>(arr, (int)((off) + (_658_i)), ((_this).data)[(int)((_this.pos) + (_658_i))]));
        }
      }
      foreach (var _tup0 in _ingredients0) {
        _tup0.Item1[_tup0.Item2] = _tup0.Item3;
      }
      (_this).pos = (_this.pos) + (_657_n);
      res = @STL.Result<BigInteger>.create_Success(_657_n);
return res;
      return res;
    }
    public Dafny.Sequence<byte> ReadSeq(BigInteger desiredByteCount)
    {
      var _this = this;
    TAIL_CALL_START: ;
Dafny.Sequence<byte> bytes = Dafny.Sequence<byte>.Empty;
      BigInteger _659_n;
      _659_n = STL.__default.min(desiredByteCount, (_this).Available());
      bytes = ((System.Func<Dafny.Sequence<byte>>) (() => {
        BigInteger dim5 = _659_n;
var arr5 = new byte[(int)(dim5)];
for (int i5 = 0; i5 < dim5; i5++) { 
          var _660_i = (BigInteger) i5;
arr5[(int)(_660_i)] = ((_this).data)[(int)((_this.pos) + (_660_i))];
        }
        return Dafny.Sequence<byte>.FromArray(arr5);
      }))();
      (_this).pos = (_this.pos) + (_659_n);
      return bytes;
    }
    public STL.Result<Dafny.Sequence<byte>> ReadExact(BigInteger n)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<Dafny.Sequence<byte>> res = STL.Result<Dafny.Sequence<byte>>.Default;
      Dafny.Sequence<byte> _661_bytes;
Dafny.Sequence<byte> _out7;
var _outcollector7 = (_this).ReadSeq(n);
_out7 = _outcollector7;
_661_bytes = _out7;
      if ((new BigInteger((_661_bytes).Count)) != (n)) {
        res = @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("IO Error: Not enough bytes left on stream."));
return res;
      } else {
        res = @STL.Result<Dafny.Sequence<byte>>.create_Success(_661_bytes);
return res;
      }
      return res;
    }
    public STL.Result<byte> ReadByte()
    {
      STL.Result<byte> res = STL.Result<byte>.Default;
      Dafny.Sequence<byte> _662_bytes = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _663_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out8;
var _outcollector8 = (this).ReadExact(BigInteger.One);
_out8 = _outcollector8;
_663_valueOrError0 = _out8;
      if ((_663_valueOrError0).IsFailure()) {
        res = (_663_valueOrError0).PropagateFailure<byte>();
return res;
      }
      _662_bytes = (_663_valueOrError0).Extract();
      byte _664_n;
      _664_n = (_662_bytes).Select(BigInteger.Zero);
      res = @STL.Result<byte>.create_Success(_664_n);
return res;
      return res;
    }
    public STL.Result<ushort> ReadUInt16()
    {
      STL.Result<ushort> res = STL.Result<ushort>.Default;
      Dafny.Sequence<byte> _665_bytes = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _666_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out9;
var _outcollector9 = (this).ReadExact(new BigInteger(2));
_out9 = _outcollector9;
_666_valueOrError0 = _out9;
      if ((_666_valueOrError0).IsFailure()) {
        res = (_666_valueOrError0).PropagateFailure<ushort>();
return res;
      }
      _665_bytes = (_666_valueOrError0).Extract();
      ushort _667_n;
      _667_n = STLUInt.__default.SeqToUInt16(_665_bytes);
      res = @STL.Result<ushort>.create_Success(_667_n);
return res;
      return res;
    }
    public STL.Result<uint> ReadUInt32()
    {
      STL.Result<uint> res = STL.Result<uint>.Default;
      Dafny.Sequence<byte> _668_bytes = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _669_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out10;
var _outcollector10 = (this).ReadExact(new BigInteger(4));
_out10 = _outcollector10;
_669_valueOrError0 = _out10;
      if ((_669_valueOrError0).IsFailure()) {
        res = (_669_valueOrError0).PropagateFailure<uint>();
return res;
      }
      _668_bytes = (_669_valueOrError0).Extract();
      uint _670_n;
      _670_n = STLUInt.__default.SeqToUInt32(_668_bytes);
      res = @STL.Result<uint>.create_Success(_670_n);
return res;
      return res;
    }
    public byte[] _data = new byte[0];
public byte[] data { get {
      return this._data;
    } }
  }

  public partial class StringWriter {
    public Dafny.Sequence<byte> data = Dafny.Sequence<byte>.Empty;
public bool HasRemainingCapacity(BigInteger n) {
      return true;
    }
    public void __ctor()
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).data = Dafny.Sequence<byte>.FromElements();
      { }
    }
    public STL.Result<BigInteger> Write(byte[] a, BigInteger off, BigInteger len)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<BigInteger> res = STL.Result<BigInteger>.Default;
      if ((_this).HasRemainingCapacity(len)) {
        (_this).data = (_this.data).Concat((Dafny.Helpers.SeqFromArray(a).Subsequence(off, (off) + (len))));
        res = @STL.Result<BigInteger>.create_Success(len);
return res;
      } else {
        res = @STL.Result<BigInteger>.create_Failure(Dafny.Sequence<char>.FromString("IO Error: Stream capacity exceeded."));
return res;
      }
      return res;
    }
    public STL.Result<BigInteger> WriteSeq(Dafny.Sequence<byte> bytes)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<BigInteger> res = STL.Result<BigInteger>.Default;
      if ((_this).HasRemainingCapacity(new BigInteger((bytes).Count))) {
        (_this).data = (_this.data).Concat((bytes));
        res = @STL.Result<BigInteger>.create_Success(new BigInteger((bytes).Count));
return res;
      } else {
        res = @STL.Result<BigInteger>.create_Failure(Dafny.Sequence<char>.FromString("IO Error: Stream capacity exceeded."));
return res;
      }
      return res;
    }
    public STL.Result<BigInteger> WriteByte(byte n)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<BigInteger> res = STL.Result<BigInteger>.Default;
      if ((_this).HasRemainingCapacity(BigInteger.One)) {
        (_this).data = (_this.data).Concat((Dafny.Sequence<byte>.FromElements(n)));
        res = @STL.Result<BigInteger>.create_Success(BigInteger.One);
return res;
      } else {
        res = @STL.Result<BigInteger>.create_Failure(Dafny.Sequence<char>.FromString("IO Error: Stream capacity exceeded."));
return res;
      }
      return res;
    }
    public STL.Result<BigInteger> WriteUInt16(ushort n)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<BigInteger> res = STL.Result<BigInteger>.Default;
      if ((_this).HasRemainingCapacity(new BigInteger(2))) {
        (_this).data = (_this.data).Concat((STLUInt.__default.UInt16ToSeq(n)));
        res = @STL.Result<BigInteger>.create_Success(new BigInteger(2));
return res;
      } else {
        res = @STL.Result<BigInteger>.create_Failure(Dafny.Sequence<char>.FromString("IO Error: Stream capacity exceeded."));
return res;
      }
      return res;
    }
    public STL.Result<BigInteger> WriteUInt32(uint n)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<BigInteger> res = STL.Result<BigInteger>.Default;
      if ((_this).HasRemainingCapacity(new BigInteger(4))) {
        (_this).data = (_this.data).Concat((STLUInt.__default.UInt32ToSeq(n)));
        res = @STL.Result<BigInteger>.create_Success(new BigInteger(4));
return res;
      } else {
        res = @STL.Result<BigInteger>.create_Failure(Dafny.Sequence<char>.FromString("IO Error: Stream capacity exceeded."));
return res;
      }
      return res;
    }
  }

} // end of namespace _54_Streams_Compile
namespace Random {




} // end of namespace Random
namespace AESEncryption {





  public class EncryptionOutput {
    public readonly Dafny.Sequence<byte> cipherText;
public readonly Dafny.Sequence<byte> authTag;
public EncryptionOutput(Dafny.Sequence<byte> cipherText, Dafny.Sequence<byte> authTag) {
      this.cipherText = cipherText;
this.authTag = authTag;
    }
    public override bool Equals(object other) {
      var oth = other as AESEncryption.EncryptionOutput;
return oth != null && object.Equals(this.cipherText, oth.cipherText) && object.Equals(this.authTag, oth.authTag);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cipherText));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.authTag));
return (int) hash;
    }
    public override string ToString() {
      string s = "AESEncryption_Compile.EncryptionOutput.EncryptionOutput";
s += "(";
s += Dafny.Helpers.ToString(this.cipherText);
s += ", ";
s += Dafny.Helpers.ToString(this.authTag);
s += ")";
return s;
    }
    static EncryptionOutput theDefault;
public static EncryptionOutput Default {
      get {
        if (theDefault == null) {
          theDefault = new AESEncryption.EncryptionOutput(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
        }
        return theDefault;
      }
    }
    public static EncryptionOutput _DafnyDefaultValue() { return Default; }
public static EncryptionOutput create(Dafny.Sequence<byte> cipherText, Dafny.Sequence<byte> authTag) {
      return new EncryptionOutput(cipherText, authTag);
    }
    public bool is_EncryptionOutput { get { return true; } }
public Dafny.Sequence<byte> dtor_cipherText {
      get {
        return this.cipherText;
      }
    }
    public Dafny.Sequence<byte> dtor_authTag {
      get {
        return this.authTag;
      }
    }
  }

  public partial class __default {
    public static AESEncryption.EncryptionOutput EncryptionOutputFromByteSeq(Dafny.Sequence<byte> s, EncryptionSuites.EncryptionSuite encAlg)
    {
      return @AESEncryption.EncryptionOutput.create((s).Take((new BigInteger((s).Count)) - (new BigInteger((encAlg).dtor_tagLen))), (s).Drop((new BigInteger((s).Count)) - (new BigInteger((encAlg).dtor_tagLen))));
    }
  }
} // end of namespace AESEncryption
namespace _76_MessageHeader_Compile {






  public class Header {
    public readonly _76_MessageHeader_Compile.HeaderBody body;
public readonly _76_MessageHeader_Compile.HeaderAuthentication auth;
public Header(_76_MessageHeader_Compile.HeaderBody body, _76_MessageHeader_Compile.HeaderAuthentication auth) {
      this.body = body;
this.auth = auth;
    }
    public override bool Equals(object other) {
      var oth = other as _76_MessageHeader_Compile.Header;
return oth != null && object.Equals(this.body, oth.body) && object.Equals(this.auth, oth.auth);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.body));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.auth));
return (int) hash;
    }
    public override string ToString() {
      string s = "_76_MessageHeader_Compile.Header.Header";
s += "(";
s += Dafny.Helpers.ToString(this.body);
s += ", ";
s += Dafny.Helpers.ToString(this.auth);
s += ")";
return s;
    }
    static Header theDefault;
public static Header Default {
      get {
        if (theDefault == null) {
          theDefault = new _76_MessageHeader_Compile.Header(_76_MessageHeader_Compile.HeaderBody.Default, _76_MessageHeader_Compile.HeaderAuthentication.Default);
        }
        return theDefault;
      }
    }
    public static Header _DafnyDefaultValue() { return Default; }
public static Header create(_76_MessageHeader_Compile.HeaderBody body, _76_MessageHeader_Compile.HeaderAuthentication auth) {
      return new Header(body, auth);
    }
    public bool is_Header { get { return true; } }
public _76_MessageHeader_Compile.HeaderBody dtor_body {
      get {
        return this.body;
      }
    }
    public _76_MessageHeader_Compile.HeaderAuthentication dtor_auth {
      get {
        return this.auth;
      }
    }
  }

  public partial class Version {
    public static readonly byte Witness = _76_MessageHeader_Compile.__default.VERSION__1;
  }

  public partial class Type {
    public static readonly byte Witness = _76_MessageHeader_Compile.__default.TYPE__CUSTOMER__AED;
  }

  public partial class MessageID {
    public static readonly Dafny.Sequence<byte> Witness = Dafny.Sequence<byte>.FromElements(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
  }

  public abstract class ContentType {
    public ContentType() { }
static ContentType theDefault;
public static ContentType Default {
      get {
        if (theDefault == null) {
          theDefault = new _76_MessageHeader_Compile.ContentType_NonFramed();
        }
        return theDefault;
      }
    }
    public static ContentType _DafnyDefaultValue() { return Default; }
public static ContentType create_NonFramed() {
      return new ContentType_NonFramed();
    }
    public static ContentType create_Framed() {
      return new ContentType_Framed();
    }
    public bool is_NonFramed { get { return this is ContentType_NonFramed; } }
public bool is_Framed { get { return this is ContentType_Framed; } }
public static System.Collections.Generic.IEnumerable<ContentType> AllSingletonConstructors {
      get {
        yield return ContentType.create_NonFramed();
yield return ContentType.create_Framed();
      }
    }
  }
  public class ContentType_NonFramed : ContentType {
    public ContentType_NonFramed() {
    }
    public override bool Equals(object other) {
      var oth = other as _76_MessageHeader_Compile.ContentType_NonFramed;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
return (int) hash;
    }
    public override string ToString() {
      string s = "_76_MessageHeader_Compile.ContentType.NonFramed";
return s;
    }
  }
  public class ContentType_Framed : ContentType {
    public ContentType_Framed() {
    }
    public override bool Equals(object other) {
      var oth = other as _76_MessageHeader_Compile.ContentType_Framed;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
return (int) hash;
    }
    public override string ToString() {
      string s = "_76_MessageHeader_Compile.ContentType.Framed";
return s;
    }
  }

  public class EncryptedDataKeys {
    public readonly Dafny.Sequence<Materials.EncryptedDataKey> entries;
public EncryptedDataKeys(Dafny.Sequence<Materials.EncryptedDataKey> entries) {
      this.entries = entries;
    }
    public override bool Equals(object other) {
      var oth = other as _76_MessageHeader_Compile.EncryptedDataKeys;
return oth != null && object.Equals(this.entries, oth.entries);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.entries));
return (int) hash;
    }
    public override string ToString() {
      string s = "_76_MessageHeader_Compile.EncryptedDataKeys.EncryptedDataKeys";
s += "(";
s += Dafny.Helpers.ToString(this.entries);
s += ")";
return s;
    }
    static EncryptedDataKeys theDefault;
public static EncryptedDataKeys Default {
      get {
        if (theDefault == null) {
          theDefault = new _76_MessageHeader_Compile.EncryptedDataKeys(Dafny.Sequence<Materials.EncryptedDataKey>.Empty);
        }
        return theDefault;
      }
    }
    public static EncryptedDataKeys _DafnyDefaultValue() { return Default; }
public static EncryptedDataKeys create(Dafny.Sequence<Materials.EncryptedDataKey> entries) {
      return new EncryptedDataKeys(entries);
    }
    public bool is_EncryptedDataKeys { get { return true; } }
public Dafny.Sequence<Materials.EncryptedDataKey> dtor_entries {
      get {
        return this.entries;
      }
    }
  }

  public class HeaderBody {
    public readonly byte version;
public readonly byte typ;
public readonly ushort algorithmSuiteID;
public readonly Dafny.Sequence<byte> messageID;
public readonly Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> aad;
public readonly _76_MessageHeader_Compile.EncryptedDataKeys encryptedDataKeys;
public readonly _76_MessageHeader_Compile.ContentType contentType;
public readonly byte ivLength;
public readonly uint frameLength;
public HeaderBody(byte version, byte typ, ushort algorithmSuiteID, Dafny.Sequence<byte> messageID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> aad, _76_MessageHeader_Compile.EncryptedDataKeys encryptedDataKeys, _76_MessageHeader_Compile.ContentType contentType, byte ivLength, uint frameLength) {
      this.version = version;
this.typ = typ;
this.algorithmSuiteID = algorithmSuiteID;
this.messageID = messageID;
this.aad = aad;
this.encryptedDataKeys = encryptedDataKeys;
this.contentType = contentType;
this.ivLength = ivLength;
this.frameLength = frameLength;
    }
    public override bool Equals(object other) {
      var oth = other as _76_MessageHeader_Compile.HeaderBody;
return oth != null && this.version == oth.version && this.typ == oth.typ && this.algorithmSuiteID == oth.algorithmSuiteID && object.Equals(this.messageID, oth.messageID) && object.Equals(this.aad, oth.aad) && object.Equals(this.encryptedDataKeys, oth.encryptedDataKeys) && object.Equals(this.contentType, oth.contentType) && this.ivLength == oth.ivLength && this.frameLength == oth.frameLength;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.version));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.typ));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithmSuiteID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.messageID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.aad));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptedDataKeys));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.contentType));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ivLength));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.frameLength));
return (int) hash;
    }
    public override string ToString() {
      string s = "_76_MessageHeader_Compile.HeaderBody.HeaderBody";
s += "(";
s += Dafny.Helpers.ToString(this.version);
s += ", ";
s += Dafny.Helpers.ToString(this.typ);
s += ", ";
s += Dafny.Helpers.ToString(this.algorithmSuiteID);
s += ", ";
s += Dafny.Helpers.ToString(this.messageID);
s += ", ";
s += Dafny.Helpers.ToString(this.aad);
s += ", ";
s += Dafny.Helpers.ToString(this.encryptedDataKeys);
s += ", ";
s += Dafny.Helpers.ToString(this.contentType);
s += ", ";
s += Dafny.Helpers.ToString(this.ivLength);
s += ", ";
s += Dafny.Helpers.ToString(this.frameLength);
s += ")";
return s;
    }
    static HeaderBody theDefault;
public static HeaderBody Default {
      get {
        if (theDefault == null) {
          theDefault = new _76_MessageHeader_Compile.HeaderBody(_76_MessageHeader_Compile.Version.Witness, _76_MessageHeader_Compile.Type.Witness, _25_AlgorithmSuite_Compile.ID.Witness, _76_MessageHeader_Compile.MessageID.Witness, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.Empty, _76_MessageHeader_Compile.EncryptedDataKeys.Default, _76_MessageHeader_Compile.ContentType.Default, 0, 0);
        }
        return theDefault;
      }
    }
    public static HeaderBody _DafnyDefaultValue() { return Default; }
public static HeaderBody create(byte version, byte typ, ushort algorithmSuiteID, Dafny.Sequence<byte> messageID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> aad, _76_MessageHeader_Compile.EncryptedDataKeys encryptedDataKeys, _76_MessageHeader_Compile.ContentType contentType, byte ivLength, uint frameLength) {
      return new HeaderBody(version, typ, algorithmSuiteID, messageID, aad, encryptedDataKeys, contentType, ivLength, frameLength);
    }
    public bool is_HeaderBody { get { return true; } }
public byte dtor_version {
      get {
        return this.version;
      }
    }
    public byte dtor_typ {
      get {
        return this.typ;
      }
    }
    public ushort dtor_algorithmSuiteID {
      get {
        return this.algorithmSuiteID;
      }
    }
    public Dafny.Sequence<byte> dtor_messageID {
      get {
        return this.messageID;
      }
    }
    public Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> dtor_aad {
      get {
        return this.aad;
      }
    }
    public _76_MessageHeader_Compile.EncryptedDataKeys dtor_encryptedDataKeys {
      get {
        return this.encryptedDataKeys;
      }
    }
    public _76_MessageHeader_Compile.ContentType dtor_contentType {
      get {
        return this.contentType;
      }
    }
    public byte dtor_ivLength {
      get {
        return this.ivLength;
      }
    }
    public uint dtor_frameLength {
      get {
        return this.frameLength;
      }
    }
  }

  public class HeaderAuthentication {
    public readonly Dafny.Sequence<byte> iv;
public readonly Dafny.Sequence<byte> authenticationTag;
public HeaderAuthentication(Dafny.Sequence<byte> iv, Dafny.Sequence<byte> authenticationTag) {
      this.iv = iv;
this.authenticationTag = authenticationTag;
    }
    public override bool Equals(object other) {
      var oth = other as _76_MessageHeader_Compile.HeaderAuthentication;
return oth != null && object.Equals(this.iv, oth.iv) && object.Equals(this.authenticationTag, oth.authenticationTag);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.iv));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.authenticationTag));
return (int) hash;
    }
    public override string ToString() {
      string s = "_76_MessageHeader_Compile.HeaderAuthentication.HeaderAuthentication";
s += "(";
s += Dafny.Helpers.ToString(this.iv);
s += ", ";
s += Dafny.Helpers.ToString(this.authenticationTag);
s += ")";
return s;
    }
    static HeaderAuthentication theDefault;
public static HeaderAuthentication Default {
      get {
        if (theDefault == null) {
          theDefault = new _76_MessageHeader_Compile.HeaderAuthentication(Dafny.Sequence<byte>.Empty, Dafny.Sequence<byte>.Empty);
        }
        return theDefault;
      }
    }
    public static HeaderAuthentication _DafnyDefaultValue() { return Default; }
public static HeaderAuthentication create(Dafny.Sequence<byte> iv, Dafny.Sequence<byte> authenticationTag) {
      return new HeaderAuthentication(iv, authenticationTag);
    }
    public bool is_HeaderAuthentication { get { return true; } }
public Dafny.Sequence<byte> dtor_iv {
      get {
        return this.iv;
      }
    }
    public Dafny.Sequence<byte> dtor_authenticationTag {
      get {
        return this.authenticationTag;
      }
    }
  }

  public partial class __default {
    public static byte ContentTypeToUInt8(_76_MessageHeader_Compile.ContentType contentType) {
      _76_MessageHeader_Compile.ContentType _source6 = contentType;
if (_source6.is_NonFramed) {
        return 1;
      } else {
        return 2;
      }
    }
    public static STL.Option<_76_MessageHeader_Compile.ContentType> UInt8ToContentType(byte x) {
      if ((x) == (1)) {
        return @STL.Option<_76_MessageHeader_Compile.ContentType>.create_Some(@_76_MessageHeader_Compile.ContentType.create_NonFramed());
      } else  {
        if ((x) == (2)) {
          return @STL.Option<_76_MessageHeader_Compile.ContentType>.create_Some(@_76_MessageHeader_Compile.ContentType.create_Framed());
        } else  {
          return @STL.Option<_76_MessageHeader_Compile.ContentType>.create_None();
        }
      }
    }
    public static byte VERSION__1 { get {
      return 1;
    } }
    public static byte TYPE__CUSTOMER__AED { get {
      return 128;
    } }
    public static BigInteger MESSAGE__ID__LEN { get {
      return new BigInteger(16);
    } }
    public static Dafny.Sequence<byte> Reserved { get {
      return Dafny.Sequence<byte>.FromElements(0, 0, 0, 0);
    } }
  }
} // end of namespace _76_MessageHeader_Compile
namespace _83_Serialize_Compile {







  public partial class __default {
    public static STL.Result<BigInteger> SerializeHeaderBody(_54_Streams_Compile.StringWriter wr, _76_MessageHeader_Compile.HeaderBody hb)
    {
      STL.Result<BigInteger> ret = STL.Result<BigInteger>.Default;
      BigInteger _671_totalWritten;
      _671_totalWritten = BigInteger.Zero;
      BigInteger _672_len = BigInteger.Zero;
      STL.Result<BigInteger> _673_valueOrError0;
STL.Result<BigInteger> _out11;
var _outcollector11 = (wr).WriteByte((byte)((hb).dtor_version));
_out11 = _outcollector11;
_673_valueOrError0 = _out11;
      if ((_673_valueOrError0).IsFailure()) {
        ret = (_673_valueOrError0).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_673_valueOrError0).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      STL.Result<BigInteger> _674_valueOrError1;
STL.Result<BigInteger> _out12;
var _outcollector12 = (wr).WriteByte((byte)((hb).dtor_typ));
_out12 = _outcollector12;
_674_valueOrError1 = _out12;
      if ((_674_valueOrError1).IsFailure()) {
        ret = (_674_valueOrError1).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_674_valueOrError1).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      STL.Result<BigInteger> _675_valueOrError2;
STL.Result<BigInteger> _out13;
var _outcollector13 = (wr).WriteUInt16((ushort)((hb).dtor_algorithmSuiteID));
_out13 = _outcollector13;
_675_valueOrError2 = _out13;
      if ((_675_valueOrError2).IsFailure()) {
        ret = (_675_valueOrError2).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_675_valueOrError2).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      STL.Result<BigInteger> _676_valueOrError3;
STL.Result<BigInteger> _out14;
var _outcollector14 = (wr).WriteSeq((hb).dtor_messageID);
_out14 = _outcollector14;
_676_valueOrError3 = _out14;
      if ((_676_valueOrError3).IsFailure()) {
        ret = (_676_valueOrError3).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_676_valueOrError3).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      STL.Result<BigInteger> _677_valueOrError4;
STL.Result<BigInteger> _out15;
var _outcollector15 = _83_Serialize_Compile.__default.SerializeAAD(wr, (hb).dtor_aad);
_out15 = _outcollector15;
_677_valueOrError4 = _out15;
      if ((_677_valueOrError4).IsFailure()) {
        ret = (_677_valueOrError4).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_677_valueOrError4).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      STL.Result<BigInteger> _678_valueOrError5;
STL.Result<BigInteger> _out16;
var _outcollector16 = _83_Serialize_Compile.__default.SerializeEDKs(wr, (hb).dtor_encryptedDataKeys);
_out16 = _outcollector16;
_678_valueOrError5 = _out16;
      if ((_678_valueOrError5).IsFailure()) {
        ret = (_678_valueOrError5).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_678_valueOrError5).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      byte _679_contentType;
      _679_contentType = _76_MessageHeader_Compile.__default.ContentTypeToUInt8((hb).dtor_contentType);
      STL.Result<BigInteger> _680_valueOrError6;
STL.Result<BigInteger> _out17;
var _outcollector17 = (wr).WriteByte(_679_contentType);
_out17 = _outcollector17;
_680_valueOrError6 = _out17;
      if ((_680_valueOrError6).IsFailure()) {
        ret = (_680_valueOrError6).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_680_valueOrError6).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      STL.Result<BigInteger> _681_valueOrError7;
STL.Result<BigInteger> _out18;
var _outcollector18 = (wr).WriteSeq(_76_MessageHeader_Compile.__default.Reserved);
_out18 = _outcollector18;
_681_valueOrError7 = _out18;
      if ((_681_valueOrError7).IsFailure()) {
        ret = (_681_valueOrError7).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_681_valueOrError7).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      STL.Result<BigInteger> _682_valueOrError8;
STL.Result<BigInteger> _out19;
var _outcollector19 = (wr).WriteByte((hb).dtor_ivLength);
_out19 = _outcollector19;
_682_valueOrError8 = _out19;
      if ((_682_valueOrError8).IsFailure()) {
        ret = (_682_valueOrError8).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_682_valueOrError8).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      STL.Result<BigInteger> _683_valueOrError9;
STL.Result<BigInteger> _out20;
var _outcollector20 = (wr).WriteUInt32((hb).dtor_frameLength);
_out20 = _outcollector20;
_683_valueOrError9 = _out20;
      if ((_683_valueOrError9).IsFailure()) {
        ret = (_683_valueOrError9).PropagateFailure<BigInteger>();
return ret;
      }
      _672_len = (_683_valueOrError9).Extract();
      _671_totalWritten = (_671_totalWritten) + (_672_len);
      { }
      ret = @STL.Result<BigInteger>.create_Success(_671_totalWritten);
return ret;
      return ret;
    }
    public static STL.Result<BigInteger> SerializeHeaderAuthentication(_54_Streams_Compile.StringWriter wr, _76_MessageHeader_Compile.HeaderAuthentication ha)
    {
      STL.Result<BigInteger> ret = STL.Result<BigInteger>.Default;
      BigInteger _684_m = BigInteger.Zero;
      STL.Result<BigInteger> _685_valueOrError0;
STL.Result<BigInteger> _out21;
var _outcollector21 = (wr).WriteSeq((ha).dtor_iv);
_out21 = _outcollector21;
_685_valueOrError0 = _out21;
      if ((_685_valueOrError0).IsFailure()) {
        ret = (_685_valueOrError0).PropagateFailure<BigInteger>();
return ret;
      }
      _684_m = (_685_valueOrError0).Extract();
      BigInteger _686_n = BigInteger.Zero;
      STL.Result<BigInteger> _687_valueOrError1;
STL.Result<BigInteger> _out22;
var _outcollector22 = (wr).WriteSeq((ha).dtor_authenticationTag);
_out22 = _outcollector22;
_687_valueOrError1 = _out22;
      if ((_687_valueOrError1).IsFailure()) {
        ret = (_687_valueOrError1).PropagateFailure<BigInteger>();
return ret;
      }
      _686_n = (_687_valueOrError1).Extract();
      ret = @STL.Result<BigInteger>.create_Success((_684_m) + (_686_n));
return ret;
      return ret;
    }
    public static STL.Result<BigInteger> SerializeAAD(_54_Streams_Compile.StringWriter wr, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> kvPairs)
    {
      STL.Result<BigInteger> ret = STL.Result<BigInteger>.Default;
      { }
      BigInteger _688_totalWritten;
      _688_totalWritten = BigInteger.Zero;
      ushort _689_aadLength = 0;
      STL.Result<ushort> _690_valueOrError0;
STL.Result<ushort> _out23;
var _outcollector23 = _83_Serialize_Compile.__default.ComputeAADLength(kvPairs);
_out23 = _outcollector23;
_690_valueOrError0 = _out23;
      if ((_690_valueOrError0).IsFailure()) {
        ret = (_690_valueOrError0).PropagateFailure<BigInteger>();
return ret;
      }
      _689_aadLength = (_690_valueOrError0).Extract();
      BigInteger _691_len = BigInteger.Zero;
      STL.Result<BigInteger> _692_valueOrError1;
STL.Result<BigInteger> _out24;
var _outcollector24 = (wr).WriteUInt16(_689_aadLength);
_out24 = _outcollector24;
_692_valueOrError1 = _out24;
      if ((_692_valueOrError1).IsFailure()) {
        ret = (_692_valueOrError1).PropagateFailure<BigInteger>();
return ret;
      }
      _691_len = (_692_valueOrError1).Extract();
      _688_totalWritten = (_688_totalWritten) + (_691_len);
      if ((_689_aadLength) == (0)) {
        ret = @STL.Result<BigInteger>.create_Success(_688_totalWritten);
return ret;
      }
      STL.Result<BigInteger> _693_valueOrError2;
STL.Result<BigInteger> _out25;
var _outcollector25 = (wr).WriteUInt16((ushort)(kvPairs).Count);
_out25 = _outcollector25;
_693_valueOrError2 = _out25;
      if ((_693_valueOrError2).IsFailure()) {
        ret = (_693_valueOrError2).PropagateFailure<BigInteger>();
return ret;
      }
      _691_len = (_693_valueOrError2).Extract();
      _688_totalWritten = (_688_totalWritten) + (_691_len);
      BigInteger _694_j;
      _694_j = BigInteger.Zero;
      { }
      while ((_694_j) < (new BigInteger((kvPairs).Count))) {
        STL.Result<BigInteger> _695_valueOrError3;
STL.Result<BigInteger> _out26;
var _outcollector26 = (wr).WriteUInt16((ushort)(((kvPairs).Select(_694_j)).dtor__0).Count);
_out26 = _outcollector26;
_695_valueOrError3 = _out26;
        if ((_695_valueOrError3).IsFailure()) {
          ret = (_695_valueOrError3).PropagateFailure<BigInteger>();
return ret;
        }
        _691_len = (_695_valueOrError3).Extract();
        _688_totalWritten = (_688_totalWritten) + (_691_len);
        STL.Result<BigInteger> _696_valueOrError4;
STL.Result<BigInteger> _out27;
var _outcollector27 = (wr).WriteSeq(((kvPairs).Select(_694_j)).dtor__0);
_out27 = _outcollector27;
_696_valueOrError4 = _out27;
        if ((_696_valueOrError4).IsFailure()) {
          ret = (_696_valueOrError4).PropagateFailure<BigInteger>();
return ret;
        }
        _691_len = (_696_valueOrError4).Extract();
        _688_totalWritten = (_688_totalWritten) + (_691_len);
        STL.Result<BigInteger> _697_valueOrError5;
STL.Result<BigInteger> _out28;
var _outcollector28 = (wr).WriteUInt16((ushort)(((kvPairs).Select(_694_j)).dtor__1).Count);
_out28 = _outcollector28;
_697_valueOrError5 = _out28;
        if ((_697_valueOrError5).IsFailure()) {
          ret = (_697_valueOrError5).PropagateFailure<BigInteger>();
return ret;
        }
        _691_len = (_697_valueOrError5).Extract();
        _688_totalWritten = (_688_totalWritten) + (_691_len);
        STL.Result<BigInteger> _698_valueOrError6;
STL.Result<BigInteger> _out29;
var _outcollector29 = (wr).WriteSeq(((kvPairs).Select(_694_j)).dtor__1);
_out29 = _outcollector29;
_698_valueOrError6 = _out29;
        if ((_698_valueOrError6).IsFailure()) {
          ret = (_698_valueOrError6).PropagateFailure<BigInteger>();
return ret;
        }
        _691_len = (_698_valueOrError6).Extract();
        _688_totalWritten = (_688_totalWritten) + (_691_len);
        _694_j = (_694_j) + (BigInteger.One);
      }
      ret = @STL.Result<BigInteger>.create_Success(_688_totalWritten);
return ret;
      return ret;
    }
    public static STL.Result<ushort> ComputeAADLength(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> kvPairs)
    {
    TAIL_CALL_START: ;
STL.Result<ushort> res = STL.Result<ushort>.Default;
      int _699_n;
      _699_n = (int)(kvPairs).Count;
      if ((_699_n) == (0)) {
        res = @STL.Result<ushort>.create_Success(0);
return res;
      } else {
        int _700_len;
int _701_limit;
        int _rhs0 = 2;
int _rhs1 = (int)(STLUInt.__default.UINT16__LIMIT);
_700_len = _rhs0;
_701_limit = _rhs1;
        int _702_i;
        _702_i = 0;
        while ((_702_i) < (_699_n)) {
          _System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _703_kvPair;
          _703_kvPair = (kvPairs).Select(_702_i);
          _700_len = (((_700_len) + (4)) + ((int)((_703_kvPair).dtor__0).Count)) + ((int)((_703_kvPair).dtor__1).Count);
          { }
          if ((_701_limit) <= (_700_len)) {
            res = @STL.Result<ushort>.create_Failure(Dafny.Sequence<char>.FromString("The number of bytes in encryption context exceeds the allowed maximum"));
return res;
          }
          _702_i = (_702_i) + (1);
        }
        res = @STL.Result<ushort>.create_Success((ushort)(_700_len));
return res;
      }
      return res;
    }
    public static STL.Result<BigInteger> SerializeEDKs(_54_Streams_Compile.StringWriter wr, _76_MessageHeader_Compile.EncryptedDataKeys encryptedDataKeys)
    {
      STL.Result<BigInteger> ret = STL.Result<BigInteger>.Default;
      BigInteger _704_totalWritten;
      _704_totalWritten = BigInteger.Zero;
      BigInteger _705_len = BigInteger.Zero;
      STL.Result<BigInteger> _706_valueOrError0;
STL.Result<BigInteger> _out30;
var _outcollector30 = (wr).WriteUInt16((ushort)((encryptedDataKeys).dtor_entries).Count);
_out30 = _outcollector30;
_706_valueOrError0 = _out30;
      if ((_706_valueOrError0).IsFailure()) {
        ret = (_706_valueOrError0).PropagateFailure<BigInteger>();
return ret;
      }
      _705_len = (_706_valueOrError0).Extract();
      _704_totalWritten = (_704_totalWritten) + (_705_len);
      BigInteger _707_j;
      _707_j = BigInteger.Zero;
      { }
      while ((_707_j) < (new BigInteger(((encryptedDataKeys).dtor_entries).Count))) {
        Materials.EncryptedDataKey _708_entry;
        _708_entry = ((encryptedDataKeys).dtor_entries).Select(_707_j);
        STL.Result<BigInteger> _709_valueOrError1;
STL.Result<BigInteger> _out31;
var _outcollector31 = (wr).WriteUInt16((ushort)((_708_entry).dtor_providerID).Count);
_out31 = _outcollector31;
_709_valueOrError1 = _out31;
        if ((_709_valueOrError1).IsFailure()) {
          ret = (_709_valueOrError1).PropagateFailure<BigInteger>();
return ret;
        }
        _705_len = (_709_valueOrError1).Extract();
        _704_totalWritten = (_704_totalWritten) + (_705_len);
        STL.Result<BigInteger> _710_valueOrError2;
STL.Result<BigInteger> _out32;
var _outcollector32 = (wr).WriteSeq((_708_entry).dtor_providerID);
_out32 = _outcollector32;
_710_valueOrError2 = _out32;
        if ((_710_valueOrError2).IsFailure()) {
          ret = (_710_valueOrError2).PropagateFailure<BigInteger>();
return ret;
        }
        _705_len = (_710_valueOrError2).Extract();
        _704_totalWritten = (_704_totalWritten) + (_705_len);
        STL.Result<BigInteger> _711_valueOrError3;
STL.Result<BigInteger> _out33;
var _outcollector33 = (wr).WriteUInt16((ushort)((_708_entry).dtor_providerInfo).Count);
_out33 = _outcollector33;
_711_valueOrError3 = _out33;
        if ((_711_valueOrError3).IsFailure()) {
          ret = (_711_valueOrError3).PropagateFailure<BigInteger>();
return ret;
        }
        _705_len = (_711_valueOrError3).Extract();
        _704_totalWritten = (_704_totalWritten) + (_705_len);
        STL.Result<BigInteger> _712_valueOrError4;
STL.Result<BigInteger> _out34;
var _outcollector34 = (wr).WriteSeq((_708_entry).dtor_providerInfo);
_out34 = _outcollector34;
_712_valueOrError4 = _out34;
        if ((_712_valueOrError4).IsFailure()) {
          ret = (_712_valueOrError4).PropagateFailure<BigInteger>();
return ret;
        }
        _705_len = (_712_valueOrError4).Extract();
        _704_totalWritten = (_704_totalWritten) + (_705_len);
        STL.Result<BigInteger> _713_valueOrError5;
STL.Result<BigInteger> _out35;
var _outcollector35 = (wr).WriteUInt16((ushort)((_708_entry).dtor_ciphertext).Count);
_out35 = _outcollector35;
_713_valueOrError5 = _out35;
        if ((_713_valueOrError5).IsFailure()) {
          ret = (_713_valueOrError5).PropagateFailure<BigInteger>();
return ret;
        }
        _705_len = (_713_valueOrError5).Extract();
        _704_totalWritten = (_704_totalWritten) + (_705_len);
        STL.Result<BigInteger> _714_valueOrError6;
STL.Result<BigInteger> _out36;
var _outcollector36 = (wr).WriteSeq((_708_entry).dtor_ciphertext);
_out36 = _outcollector36;
_714_valueOrError6 = _out36;
        if ((_714_valueOrError6).IsFailure()) {
          ret = (_714_valueOrError6).PropagateFailure<BigInteger>();
return ret;
        }
        _705_len = (_714_valueOrError6).Extract();
        _704_totalWritten = (_704_totalWritten) + (_705_len);
        _707_j = (_707_j) + (BigInteger.One);
      }
      ret = @STL.Result<BigInteger>.create_Success(_704_totalWritten);
return ret;
      return ret;
    }
  }
} // end of namespace _83_Serialize_Compile
namespace _85_RawAESKeyring_Compile {












  public partial class RawAESKeyring : _36_KeyringDefs_Compile.Keyring {
    public void __ctor(Dafny.Sequence<byte> @namespace, Dafny.Sequence<byte> name, Dafny.Sequence<byte> key, EncryptionSuites.EncryptionSuite wrappingAlg)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this)._keyNamespace = @namespace;
      (_this)._keyName = name;
      (_this)._wrappingKey = key;
      (_this)._wrappingAlgorithm = wrappingAlg;
      { }
    }
    public Dafny.Sequence<byte> SerializeProviderInfo(Dafny.Sequence<byte> iv) {
      return ((((this).keyName).Concat((Dafny.Sequence<byte>.FromElements(0, 0, 0, (byte)((((this).wrappingAlgorithm).dtor_tagLen) * (8)))))).Concat((Dafny.Sequence<byte>.FromElements(0, 0, 0, ((this).wrappingAlgorithm).dtor_ivLen)))).Concat((iv));
    }
    public STL.Result<STL.Option<Materials.DataKeyMaterials>> OnEncrypt(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, STL.Option<Dafny.Sequence<byte>> plaintextDataKey)
    {
      STL.Result<STL.Option<Materials.DataKeyMaterials>> res = STL.Result<STL.Option<Materials.DataKeyMaterials>>.Default;
      Dafny.Sequence<Materials.KeyringTraceEntry> _715_keyringTrace;
      _715_keyringTrace = Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements();
      STL.Option<Dafny.Sequence<byte>> _716_plaintextDataKey;
      _716_plaintextDataKey = plaintextDataKey;
      if ((_716_plaintextDataKey).is_None) {
        Dafny.Sequence<byte> _717_k;
Dafny.Sequence<byte> _out37;
var _outcollector37 = Random.__default.GenerateBytes((int)(_25_AlgorithmSuite_Compile.ID.KeyLength(algorithmSuiteID)));
_out37 = _outcollector37;
_717_k = _out37;
        _716_plaintextDataKey = @STL.Option<Dafny.Sequence<byte>>.create_Some(_717_k);
        Materials.KeyringTraceEntry _718_generateTraceEntry;
        _718_generateTraceEntry = (this).GenerateTraceEntry();
        _715_keyringTrace = (_715_keyringTrace).Concat((Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_718_generateTraceEntry)));
      }
      Dafny.Sequence<byte> _719_iv;
Dafny.Sequence<byte> _out38;
var _outcollector38 = Random.__default.GenerateBytes((int)(((this).wrappingAlgorithm).dtor_ivLen));
_out38 = _outcollector38;
_719_iv = _out38;
      Dafny.Sequence<byte> _720_aad;
      _720_aad = Materials.__default.FlattenSortEncCtx(encryptionContext);
      AESEncryption.EncryptionOutput _721_encryptResult = AESEncryption.EncryptionOutput.Default;
      STL.Result<AESEncryption.EncryptionOutput> _722_valueOrError0;
STL.Result<AESEncryption.EncryptionOutput> _out39;
var _outcollector39 = AESEncryption.AES_GCM.AESEncrypt((this).wrappingAlgorithm, _719_iv, (this).wrappingKey, (_716_plaintextDataKey).dtor_get, _720_aad);
_out39 = _outcollector39;
_722_valueOrError0 = _out39;
      if ((_722_valueOrError0).IsFailure()) {
        res = (_722_valueOrError0).PropagateFailure<STL.Option<Materials.DataKeyMaterials>>();
return res;
      }
      _721_encryptResult = (_722_valueOrError0).Extract();
      Dafny.Sequence<byte> _723_encryptedKey;
      _723_encryptedKey = ((_721_encryptResult).dtor_cipherText).Concat(((_721_encryptResult).dtor_authTag));
      Dafny.Sequence<byte> _724_providerInfo;
      _724_providerInfo = (this).SerializeProviderInfo(_719_iv);
      if ((STLUInt.__default.UINT16__LIMIT) <= (new BigInteger((_724_providerInfo).Count))) {
        res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Failure(Dafny.Sequence<char>.FromString("Serialized provider info too long."));
return res;
      }
      if ((STLUInt.__default.UINT16__LIMIT) <= (new BigInteger((_723_encryptedKey).Count))) {
        res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Failure(Dafny.Sequence<char>.FromString("Encrypted data key too long."));
return res;
      }
      Materials.EncryptedDataKey _725_edk;
      _725_edk = @Materials.EncryptedDataKey.create((this).keyNamespace, _724_providerInfo, _723_encryptedKey);
      Materials.KeyringTraceEntry _726_encryptTraceEntry;
      _726_encryptTraceEntry = (this).EncryptTraceEntry();
      { }
      { }
      _715_keyringTrace = (_715_keyringTrace).Concat((Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_726_encryptTraceEntry)));
      res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Success(@STL.Option<Materials.DataKeyMaterials>.create_Some(@Materials.DataKeyMaterials.create(algorithmSuiteID, (_716_plaintextDataKey).dtor_get, Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(_725_edk), _715_keyringTrace)));
      return res;
    }
    public STL.Result<STL.Option<Materials.OnDecryptResult>> OnDecrypt(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Materials.EncryptedDataKey> edks)
    {
      STL.Result<STL.Option<Materials.OnDecryptResult>> res = STL.Result<STL.Option<Materials.OnDecryptResult>>.Default;
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("I'm guessing things go wonko here\n"));
      BigInteger _727_i;
      _727_i = BigInteger.Zero;
      while ((_727_i) < (new BigInteger((edks).Count))) {
        if ((((((edks).Select(_727_i)).dtor_providerID).Equals(((this).keyNamespace))) && ((this).ValidProviderInfo(((edks).Select(_727_i)).dtor_providerInfo))) && ((new BigInteger(((this).wrappingAlgorithm).dtor_tagLen)) <= (new BigInteger((((edks).Select(_727_i)).dtor_ciphertext).Count)))) {
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("provider info: "));
Dafny.Helpers.Print(((edks).Select(_727_i)).dtor_providerInfo);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
          Dafny.Sequence<byte> _728_iv;
          _728_iv = (this).GetIvFromProvInfo(((edks).Select(_727_i)).dtor_providerInfo);
          _54_Streams_Compile.StringWriter _729_wr;
          var _nw5 = new _54_Streams_Compile.StringWriter();
_nw5.__ctor();
          _729_wr = _nw5;
          BigInteger _730_foo = BigInteger.Zero;
          STL.Result<BigInteger> _731_valueOrError0;
STL.Result<BigInteger> _out40;
var _outcollector40 = _83_Serialize_Compile.__default.SerializeAAD(_729_wr, encryptionContext);
_out40 = _outcollector40;
_731_valueOrError0 = _out40;
          if ((_731_valueOrError0).IsFailure()) {
            res = (_731_valueOrError0).PropagateFailure<STL.Option<Materials.OnDecryptResult>>();
return res;
          }
          _730_foo = (_731_valueOrError0).Extract();
          Dafny.Sequence<byte> _732_encCtx;
          _732_encCtx = (_729_wr.data).Drop(new BigInteger(2));
          BigInteger _733_encryptedKeyLength;
          _733_encryptedKeyLength = (new BigInteger((((edks).Select(_727_i)).dtor_ciphertext).Count)) - (new BigInteger(((this).wrappingAlgorithm).dtor_tagLen));
          Dafny.Sequence<byte> _734_encryptedKey;
Dafny.Sequence<byte> _735_authTag;
          Dafny.Sequence<byte> _rhs2 = (((edks).Select(_727_i)).dtor_ciphertext).Take(_733_encryptedKeyLength);
Dafny.Sequence<byte> _rhs3 = (((edks).Select(_727_i)).dtor_ciphertext).Drop(_733_encryptedKeyLength);
_734_encryptedKey = _rhs2;
_735_authTag = _rhs3;
          Dafny.Sequence<byte> _736_ptKey = Dafny.Sequence<byte>.Empty;
          STL.Result<Dafny.Sequence<byte>> _737_valueOrError1;
STL.Result<Dafny.Sequence<byte>> _out41;
var _outcollector41 = AESEncryption.AES_GCM.AESDecrypt((this).wrappingAlgorithm, (this).wrappingKey, _734_encryptedKey, _735_authTag, _728_iv, _732_encCtx);
_out41 = _outcollector41;
_737_valueOrError1 = _out41;
          if ((_737_valueOrError1).IsFailure()) {
            res = (_737_valueOrError1).PropagateFailure<STL.Option<Materials.OnDecryptResult>>();
return res;
          }
          _736_ptKey = (_737_valueOrError1).Extract();
          Materials.KeyringTraceEntry _738_decryptTraceEntry;
          _738_decryptTraceEntry = (this).DecryptTraceEntry();
          if (_25_AlgorithmSuite_Compile.ID.ValidPlaintextDataKey(algorithmSuiteID, _736_ptKey)) {
            res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Success(@STL.Option<Materials.OnDecryptResult>.create_Some(@Materials.OnDecryptResult.create(algorithmSuiteID, _736_ptKey, Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_738_decryptTraceEntry))));
return res;
          } else {
            res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Failure(Dafny.Sequence<char>.FromString("Decryption failed: bad datakey length."));
return res;
          }
        }
        _727_i = (_727_i) + (BigInteger.One);
      }
      res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Success(@STL.Option<Materials.OnDecryptResult>.create_None());
return res;
      return res;
    }
    public bool ValidProviderInfo(Dafny.Sequence<byte> info) {
      return ((((new BigInteger((info).Count)) == ((((new BigInteger(((this).keyName).Count)) + (_85_RawAESKeyring_Compile.__default.AUTH__TAG__LEN__LEN)) + (_85_RawAESKeyring_Compile.__default.IV__LEN__LEN)) + (new BigInteger(((this).wrappingAlgorithm).dtor_ivLen)))) && (((info).Subsequence(BigInteger.Zero, new BigInteger(((this).keyName).Count))).Equals(((this).keyName)))) && ((STLUInt.__default.SeqToUInt32((info).Subsequence(new BigInteger(((this).keyName).Count), (new BigInteger(((this).keyName).Count)) + (_85_RawAESKeyring_Compile.__default.AUTH__TAG__LEN__LEN)))) == (((uint)(((this).wrappingAlgorithm).dtor_tagLen)) * (8U)))) && ((STLUInt.__default.SeqToUInt32((info).Subsequence((new BigInteger(((this).keyName).Count)) + (_85_RawAESKeyring_Compile.__default.AUTH__TAG__LEN__LEN), ((new BigInteger(((this).keyName).Count)) + (_85_RawAESKeyring_Compile.__default.AUTH__TAG__LEN__LEN)) + (_85_RawAESKeyring_Compile.__default.IV__LEN__LEN)))) == ((uint)(((this).wrappingAlgorithm).dtor_ivLen)));
    }
    public Dafny.Sequence<byte> GetIvFromProvInfo(Dafny.Sequence<byte> info) {
      return (info).Drop(((new BigInteger(((this).keyName).Count)) + (_85_RawAESKeyring_Compile.__default.AUTH__TAG__LEN__LEN)) + (_85_RawAESKeyring_Compile.__default.IV__LEN__LEN));
    }
    public Materials.KeyringTraceEntry GenerateTraceEntry() {
      return @Materials.KeyringTraceEntry.create((this).keyNamespace, (this).keyName, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_GENERATED__DATA__KEY()));
    }
    public Materials.KeyringTraceEntry EncryptTraceEntry() {
      return @Materials.KeyringTraceEntry.create((this).keyNamespace, (this).keyName, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_ENCRYPTED__DATA__KEY(), @Materials.KeyringTraceFlag.create_SIGNED__ENCRYPTION__CONTEXT()));
    }
    public Materials.KeyringTraceEntry DecryptTraceEntry() {
      return @Materials.KeyringTraceEntry.create((this).keyNamespace, (this).keyName, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_DECRYPTED__DATA__KEY(), @Materials.KeyringTraceFlag.create_VERIFIED__ENCRYPTION__CONTEXT()));
    }
    public Dafny.Sequence<byte> _keyNamespace = UTF8.ValidUTF8Bytes.Witness;
public Dafny.Sequence<byte> keyNamespace { get {
      return this._keyNamespace;
    } }
    public Dafny.Sequence<byte> _keyName = UTF8.ValidUTF8Bytes.Witness;
public Dafny.Sequence<byte> keyName { get {
      return this._keyName;
    } }
    public Dafny.Sequence<byte> _wrappingKey = Dafny.Sequence<byte>.Empty;
public Dafny.Sequence<byte> wrappingKey { get {
      return this._wrappingKey;
    } }
    public EncryptionSuites.EncryptionSuite _wrappingAlgorithm = EncryptionSuites.EncryptionSuite.Default;
public EncryptionSuites.EncryptionSuite wrappingAlgorithm { get {
      return this._wrappingAlgorithm;
    } }
  }

  public partial class __default {
    public static Dafny.Set<EncryptionSuites.EncryptionSuite> VALID__ALGORITHMS { get {
      return Dafny.Set<EncryptionSuites.EncryptionSuite>.FromElements(EncryptionSuites.__default.AES__GCM__128, EncryptionSuites.__default.AES__GCM__192, EncryptionSuites.__default.AES__GCM__256);
    } }
    public static BigInteger AUTH__TAG__LEN__LEN { get {
      return new BigInteger(4);
    } }
    public static BigInteger IV__LEN__LEN { get {
      return new BigInteger(4);
    } }
  }
} // end of namespace _85_RawAESKeyring_Compile
namespace RSAEncryption {



  public abstract class RSAPaddingMode {
    public RSAPaddingMode() { }
static RSAPaddingMode theDefault;
public static RSAPaddingMode Default {
      get {
        if (theDefault == null) {
          theDefault = new RSAEncryption.RSAPaddingMode_PKCS1();
        }
        return theDefault;
      }
    }
    public static RSAPaddingMode _DafnyDefaultValue() { return Default; }
public static RSAPaddingMode create_PKCS1() {
      return new RSAPaddingMode_PKCS1();
    }
    public static RSAPaddingMode create_OAEP__SHA1() {
      return new RSAPaddingMode_OAEP__SHA1();
    }
    public static RSAPaddingMode create_OAEP__SHA256() {
      return new RSAPaddingMode_OAEP__SHA256();
    }
    public bool is_PKCS1 { get { return this is RSAPaddingMode_PKCS1; } }
public bool is_OAEP__SHA1 { get { return this is RSAPaddingMode_OAEP__SHA1; } }
public bool is_OAEP__SHA256 { get { return this is RSAPaddingMode_OAEP__SHA256; } }
public static System.Collections.Generic.IEnumerable<RSAPaddingMode> AllSingletonConstructors {
      get {
        yield return RSAPaddingMode.create_PKCS1();
yield return RSAPaddingMode.create_OAEP__SHA1();
yield return RSAPaddingMode.create_OAEP__SHA256();
      }
    }
  }
  public class RSAPaddingMode_PKCS1 : RSAPaddingMode {
    public RSAPaddingMode_PKCS1() {
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.RSAPaddingMode_PKCS1;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.RSAPaddingMode.PKCS1";
return s;
    }
  }
  public class RSAPaddingMode_OAEP__SHA1 : RSAPaddingMode {
    public RSAPaddingMode_OAEP__SHA1() {
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.RSAPaddingMode_OAEP__SHA1;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 1;
return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.RSAPaddingMode.OAEP_SHA1";
return s;
    }
  }
  public class RSAPaddingMode_OAEP__SHA256 : RSAPaddingMode {
    public RSAPaddingMode_OAEP__SHA256() {
    }
    public override bool Equals(object other) {
      var oth = other as RSAEncryption.RSAPaddingMode_OAEP__SHA256;
return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 2;
return (int) hash;
    }
    public override string ToString() {
      string s = "RSAEncryption_Compile.RSAPaddingMode.OAEP_SHA256";
return s;
    }
  }

  public partial class RSABitLength {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    public static readonly int Witness = (int)(new BigInteger(521));
  }

  public partial class RSA {
    public static STL.Option<BigInteger> msg__len__of__rsa__params(RSAEncryption.RSAPaddingMode padding, int bits)
    {
      RSAEncryption.RSAPaddingMode _source7 = padding;
if (_source7.is_PKCS1) {
        return @STL.Option<BigInteger>.create_Some((RSAEncryption.__default.RSACoreMsgLen(bits)) - (new BigInteger(10)));
      } else if (_source7.is_OAEP__SHA1) {
        return @STL.Option<BigInteger>.create_Some(((RSAEncryption.__default.RSACoreMsgLen(bits)) - (BigInteger.One)) - ((new BigInteger(2)) * (RSAEncryption.__default.SHA1__DIGEST__LEN)));
      } else {
        return @STL.Option<BigInteger>.create_Some(((RSAEncryption.__default.RSACoreMsgLen(bits)) - (BigInteger.One)) - ((new BigInteger(2)) * (RSAEncryption.__default.SHA256__DIGEST__LEN)));
      }
    }
  }

  public partial class __default {
    public static BigInteger RSACoreMsgLen(int bits) {
      return Dafny.Helpers.EuclideanDivision((new BigInteger(bits)) - (BigInteger.One), new BigInteger(8));
    }
    public static BigInteger SHA1__DIGEST__LEN { get {
      return new BigInteger(20);
    } }
    public static BigInteger SHA256__DIGEST__LEN { get {
      return new BigInteger(32);
    } }
  }
} // end of namespace RSAEncryption
namespace _98_RawRSAKeyringDef_Compile {









  public partial class RawRSAKeyring : _36_KeyringDefs_Compile.Keyring {
    public void __ctor(Dafny.Sequence<byte> @namespace, Dafny.Sequence<byte> name, RSAEncryption.RSAPaddingMode padding, int bits, STL.Option<Dafny.Sequence<byte>> ek, STL.Option<Dafny.Sequence<byte>> dk)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this)._keyNamespace = @namespace;
      (_this)._keyName = name;
      RSAEncryption.RSAPaddingMode _rhs4 = padding;
int _rhs5 = bits;
(_this)._paddingMode = _rhs4;
(_this)._bitLength = _rhs5;
      (_this)._encryptionKey = ek;
      (_this)._decryptionKey = dk;
      { }
    }
    public STL.Result<STL.Option<Materials.DataKeyMaterials>> OnEncrypt(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, STL.Option<Dafny.Sequence<byte>> plaintextDataKey)
    {
      var _this = this;
    TAIL_CALL_START: ;
STL.Result<STL.Option<Materials.DataKeyMaterials>> res = STL.Result<STL.Option<Materials.DataKeyMaterials>>.Default;
      if (((_this).encryptionKey).is_None) {
        res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Failure(Dafny.Sequence<char>.FromString("Encryption key undefined"));
return res;
      } else {
        STL.Option<Dafny.Sequence<byte>> _739_plaintextDataKey;
        _739_plaintextDataKey = plaintextDataKey;
        ushort _740_algorithmID;
        _740_algorithmID = algorithmSuiteID;
        Dafny.Sequence<Materials.KeyringTraceEntry> _741_keyringTrace;
        _741_keyringTrace = Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements();
        if ((_739_plaintextDataKey).is_None) {
          Dafny.Sequence<byte> _742_k;
Dafny.Sequence<byte> _out42;
var _outcollector42 = Random.__default.GenerateBytes((int)(_25_AlgorithmSuite_Compile.ID.KDFInputKeyLength(_740_algorithmID)));
_out42 = _outcollector42;
_742_k = _out42;
          _739_plaintextDataKey = @STL.Option<Dafny.Sequence<byte>>.create_Some(_742_k);
          Materials.KeyringTraceEntry _743_generateTraceEntry;
          _743_generateTraceEntry = (_this).GenerateTraceEntry();
          _741_keyringTrace = (_741_keyringTrace).Concat((Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_743_generateTraceEntry)));
        }
        Dafny.Sequence<byte> _744_aad;
        _744_aad = Materials.__default.FlattenSortEncCtx(encryptionContext);
        STL.Option<Dafny.Sequence<byte>> _745_edkCiphertext;
STL.Option<Dafny.Sequence<byte>> _out43;
var _outcollector43 = RSAEncryption.RSA.RSAEncrypt((_this).bitLength, (_this).paddingMode, ((_this).encryptionKey).dtor_get, (_739_plaintextDataKey).dtor_get);
_out43 = _outcollector43;
_745_edkCiphertext = _out43;
        if ((_745_edkCiphertext).is_None) {
          res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Failure(Dafny.Sequence<char>.FromString("Error on encrypt!"));
return res;
        } else if ((STLUInt.__default.UINT16__LIMIT) <= (new BigInteger(((_745_edkCiphertext).dtor_get).Count))) {
          res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Failure(Dafny.Sequence<char>.FromString("Encrypted data key too long."));
return res;
        }
        Materials.EncryptedDataKey _746_edk;
        _746_edk = @Materials.EncryptedDataKey.create((_this).keyNamespace, (_this).keyName, (_745_edkCiphertext).dtor_get);
        Materials.KeyringTraceEntry _747_encryptTraceEntry;
        _747_encryptTraceEntry = (_this).EncryptTraceEntry();
        { }
        { }
        _741_keyringTrace = (_741_keyringTrace).Concat((Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_747_encryptTraceEntry)));
        Materials.DataKeyMaterials _748_dataKey;
        _748_dataKey = @Materials.DataKeyMaterials.create(algorithmSuiteID, (_739_plaintextDataKey).dtor_get, Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(_746_edk), _741_keyringTrace);
        { }
        res = @STL.Result<STL.Option<Materials.DataKeyMaterials>>.create_Success(@STL.Option<Materials.DataKeyMaterials>.create_Some(_748_dataKey));
return res;
      }
      return res;
    }
    public STL.Result<STL.Option<Materials.OnDecryptResult>> OnDecrypt(ushort algorithmSuiteID, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext, Dafny.Sequence<Materials.EncryptedDataKey> edks)
    {
      STL.Result<STL.Option<Materials.OnDecryptResult>> res = STL.Result<STL.Option<Materials.OnDecryptResult>>.Default;
      if ((new BigInteger((edks).Count)).Sign == 0) {
        res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Success(@STL.Option<Materials.OnDecryptResult>.create_None());
return res;
      } else if (((this).decryptionKey).is_None) {
        res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Failure(Dafny.Sequence<char>.FromString("Decryption key undefined"));
return res;
      }
      BigInteger _749_i;
      _749_i = BigInteger.Zero;
      while ((_749_i) < (new BigInteger((edks).Count))) {
        Materials.EncryptedDataKey _750_edk;
        _750_edk = (edks).Select(_749_i);
        if (!((_750_edk).dtor_providerID).Equals(((this).keyNamespace))) {
        } else if (!((_750_edk).dtor_providerInfo).Equals(((this).keyName))) {
        } else {
          STL.Option<Dafny.Sequence<byte>> _751_octxt;
          _751_octxt = RSAEncryption.RSA.RSADecrypt((this).bitLength, (this).paddingMode, ((this).decryptionKey).dtor_get, ((edks).Select(BigInteger.Zero)).dtor_ciphertext);
          STL.Option<Dafny.Sequence<byte>> _source8 = _751_octxt;
if (_source8.is_None) {
          } else {
            Dafny.Sequence<byte> _752_k = ((STL.Option_Some<Dafny.Sequence<byte>>)_source8).@get;
            if (_25_AlgorithmSuite_Compile.ID.ValidPlaintextDataKey(algorithmSuiteID, _752_k)) {
              Materials.KeyringTraceEntry _753_decryptTraceEntry;
              _753_decryptTraceEntry = (this).DecryptTraceEntry();
              res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Success(@STL.Option<Materials.OnDecryptResult>.create_Some(@Materials.OnDecryptResult.create(algorithmSuiteID, _752_k, Dafny.Sequence<Materials.KeyringTraceEntry>.FromElements(_753_decryptTraceEntry))));
return res;
            } else {
              res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Failure(Dafny.Sequence<char>.FromString("Bad key length!"));
return res;
            }
          }
        }
        _749_i = (_749_i) + (BigInteger.One);
      }
      res = @STL.Result<STL.Option<Materials.OnDecryptResult>>.create_Success(@STL.Option<Materials.OnDecryptResult>.create_None());
return res;
      return res;
    }
    public Materials.KeyringTraceEntry GenerateTraceEntry() {
      return @Materials.KeyringTraceEntry.create((this).keyNamespace, (this).keyName, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_GENERATED__DATA__KEY()));
    }
    public Materials.KeyringTraceEntry EncryptTraceEntry() {
      return @Materials.KeyringTraceEntry.create((this).keyNamespace, (this).keyName, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_ENCRYPTED__DATA__KEY()));
    }
    public Materials.KeyringTraceEntry DecryptTraceEntry() {
      return @Materials.KeyringTraceEntry.create((this).keyNamespace, (this).keyName, Dafny.Set<Materials.KeyringTraceFlag>.FromElements(@Materials.KeyringTraceFlag.create_DECRYPTED__DATA__KEY()));
    }
    public Dafny.Sequence<byte> _keyNamespace = UTF8.ValidUTF8Bytes.Witness;
public Dafny.Sequence<byte> keyNamespace { get {
      return this._keyNamespace;
    } }
    public Dafny.Sequence<byte> _keyName = UTF8.ValidUTF8Bytes.Witness;
public Dafny.Sequence<byte> keyName { get {
      return this._keyName;
    } }
    public RSAEncryption.RSAPaddingMode _paddingMode = RSAEncryption.RSAPaddingMode.Default;
public RSAEncryption.RSAPaddingMode paddingMode { get {
      return this._paddingMode;
    } }
    public int _bitLength = RSAEncryption.RSABitLength.Witness;
public int bitLength { get {
      return this._bitLength;
    } }
    public STL.Option<Dafny.Sequence<byte>> _encryptionKey = STL.Option<Dafny.Sequence<byte>>.Default;
public STL.Option<Dafny.Sequence<byte>> encryptionKey { get {
      return this._encryptionKey;
    } }
    public STL.Option<Dafny.Sequence<byte>> _decryptionKey = STL.Option<Dafny.Sequence<byte>>.Default;
public STL.Option<Dafny.Sequence<byte>> decryptionKey { get {
      return this._decryptionKey;
    } }
  }

} // end of namespace _98_RawRSAKeyringDef_Compile
namespace _111_CMMDefs_Compile {







  public interface CMM {
    STL.Result<Materials.EncryptionMaterials> GetEncryptionMaterials(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encCtx, STL.Option<ushort> algSuiteID, STL.Option<BigInteger> plaintextLen);
STL.Result<Materials.DecryptionMaterials> DecryptMaterials(ushort algSuiteID, Dafny.Sequence<Materials.EncryptedDataKey> edks, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encCtx);
  }
  public class _Companion_CMM {
  }

} // end of namespace _111_CMMDefs_Compile
namespace _118_Base64_Compile {



  public partial class index {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
  }

  public partial class __default {
    public static bool IsBase64Char(char c) {
      BigInteger _754_i = new BigInteger(c);
return ((((_754_i) == (new BigInteger(43))) || (((new BigInteger(47)) <= (_754_i)) && ((_754_i) <= (new BigInteger(57))))) || (((new BigInteger(65)) <= (_754_i)) && ((_754_i) <= (new BigInteger(90))))) || (((new BigInteger(97)) <= (_754_i)) && ((_754_i) <= (new BigInteger(122))));
    }
    public static bool IsUnpaddedBase64String(Dafny.Sequence<char> s) {
      return ((Dafny.Helpers.EuclideanModulus(new BigInteger((s).Count), new BigInteger(4))).Sign == 0) && (Dafny.Helpers.Quantifier<char>((s).UniqueElements, true, (((_755_k) => {
        return !((s).Contains((_755_k))) || (_118_Base64_Compile.__default.IsBase64Char(_755_k));
      }))));
    }
    public static char Base64Char(byte i) {
      if ((i) == (63)) {
        return '/';
      } else  {
        if ((i) == (62)) {
          return '+';
        } else  {
          if (((52) <= (i)) && ((i) <= (61))) {
            return (char)((new BigInteger(i)) - (new BigInteger(4)));
          } else  {
            if (((26) <= (i)) && ((i) <= (51))) {
              return (char)((new BigInteger(i)) + (new BigInteger(71)));
            } else  {
              return (char)((new BigInteger(i)) + (new BigInteger(65)));
            }
          }
        }
      }
    }
    public static byte Base64Inv(char c) {
      if ((c) == ('/')) {
        return 63;
      } else  {
        if ((c) == ('+')) {
          return 62;
        } else  {
          if (((new BigInteger(48)) <= (new BigInteger(c))) && ((new BigInteger(c)) <= (new BigInteger(57)))) {
            return (byte)((new BigInteger(c)) + (new BigInteger(4)));
          } else  {
            if (((new BigInteger(65)) <= (new BigInteger(c))) && ((new BigInteger(c)) <= (new BigInteger(90)))) {
              return (byte)((new BigInteger(c)) - (new BigInteger(65)));
            } else  {
              return (byte)((new BigInteger(c)) - (new BigInteger(71)));
            }
          }
        }
      }
    }
    public static _System.Tuple3<byte,byte,byte> SplitBytes(BigInteger n) {
      BigInteger _756_n0 = Dafny.Helpers.EuclideanDivision(n, new BigInteger(65536));
BigInteger _757_m0 = (n) - ((_756_n0) * (new BigInteger(65536)));
BigInteger _758_n1 = Dafny.Helpers.EuclideanDivision(_757_m0, new BigInteger(256));
BigInteger _759_m1 = (_757_m0) - ((_758_n1) * (new BigInteger(256)));
BigInteger _760_n2 = _759_m1;
return @_System.Tuple3<byte,byte,byte>.create((byte)(_756_n0), (byte)(_758_n1), (byte)(_760_n2));
    }
    public static BigInteger CombineBytes(_System.Tuple3<byte,byte,byte> b) {
      return (((new BigInteger((b).dtor__0)) * (new BigInteger(65536))) + ((new BigInteger((b).dtor__1)) * (new BigInteger(256)))) + (new BigInteger((b).dtor__2));
    }
    public static BigInteger CombineIndices(_System.Tuple4<byte,byte,byte,byte> c) {
      return ((((new BigInteger((c).dtor__0)) * (new BigInteger(262144))) + ((new BigInteger((c).dtor__1)) * (new BigInteger(4096)))) + ((new BigInteger((c).dtor__2)) * (new BigInteger(64)))) + (new BigInteger((c).dtor__3));
    }
    public static _System.Tuple4<byte,byte,byte,byte> SplitIndices(BigInteger n) {
      BigInteger _761_n0 = Dafny.Helpers.EuclideanDivision(n, new BigInteger(262144));
BigInteger _762_m0 = (n) - ((_761_n0) * (new BigInteger(262144)));
BigInteger _763_n1 = Dafny.Helpers.EuclideanDivision(_762_m0, new BigInteger(4096));
BigInteger _764_m1 = (_762_m0) - ((_763_n1) * (new BigInteger(4096)));
BigInteger _765_n2 = Dafny.Helpers.EuclideanDivision(_764_m1, new BigInteger(64));
BigInteger _766_m2 = (_764_m1) - ((_765_n2) * (new BigInteger(64)));
BigInteger _767_n3 = _766_m2;
return @_System.Tuple4<byte,byte,byte,byte>.create((byte)(_761_n0), (byte)(_763_n1), (byte)(_765_n2), (byte)(_767_n3));
    }
    public static _System.Tuple3<byte,byte,byte> DecodeBlock(_System.Tuple4<byte,byte,byte,byte> c) {
      return _118_Base64_Compile.__default.SplitBytes(_118_Base64_Compile.__default.CombineIndices(c));
    }
    public static _System.Tuple4<byte,byte,byte,byte> EncodeBlock(_System.Tuple3<byte,byte,byte> b) {
      return _118_Base64_Compile.__default.SplitIndices(_118_Base64_Compile.__default.CombineBytes(b));
    }
    public static Dafny.Sequence<byte> DecodeRecursively(Dafny.Sequence<byte> s) {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.FromElements();
      } else  {
        _System.Tuple3<byte,byte,byte> _768_d = _118_Base64_Compile.__default.DecodeBlock(@_System.Tuple4<byte,byte,byte,byte>.create((s).Select(BigInteger.Zero), (s).Select(BigInteger.One), (s).Select(new BigInteger(2)), (s).Select(new BigInteger(3))));
return (Dafny.Sequence<byte>.FromElements((_768_d).dtor__0, (_768_d).dtor__1, (_768_d).dtor__2)).Concat((_118_Base64_Compile.__default.DecodeRecursively((s).Drop(new BigInteger(4)))));
      }
    }
    public static Dafny.Sequence<byte> EncodeRecursively(Dafny.Sequence<byte> b) {
      if ((new BigInteger((b).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.FromElements();
      } else  {
        _System.Tuple4<byte,byte,byte,byte> _769_e = _118_Base64_Compile.__default.EncodeBlock(@_System.Tuple3<byte,byte,byte>.create((b).Select(BigInteger.Zero), (b).Select(BigInteger.One), (b).Select(new BigInteger(2))));
return (Dafny.Sequence<byte>.FromElements((_769_e).dtor__0, (_769_e).dtor__1, (_769_e).dtor__2, (_769_e).dtor__3)).Concat((_118_Base64_Compile.__default.EncodeRecursively((b).Drop(new BigInteger(3)))));
      }
    }
    public static Dafny.Sequence<byte> FromCharsToIndices(Dafny.Sequence<char> s) {
      return ((System.Func<Dafny.Sequence<byte>>) (() => {
        BigInteger dim6 = new BigInteger((s).Count);
var arr6 = new byte[(int)(dim6)];
for (int i6 = 0; i6 < dim6; i6++) { 
          var _770_i = (BigInteger) i6;
arr6[(int)(_770_i)] = _118_Base64_Compile.__default.Base64Inv((s).Select(_770_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr6);
      }))();
    }
    public static Dafny.Sequence<char> FromIndicesToChars(Dafny.Sequence<byte> b) {
      return ((System.Func<Dafny.Sequence<char>>) (() => {
        BigInteger dim7 = new BigInteger((b).Count);
var arr7 = new char[(int)(dim7)];
for (int i7 = 0; i7 < dim7; i7++) { 
          var _771_i = (BigInteger) i7;
arr7[(int)(_771_i)] = _118_Base64_Compile.__default.Base64Char((b).Select(_771_i));
        }
        return Dafny.Sequence<char>.FromArray(arr7);
      }))();
    }
    public static Dafny.Sequence<byte> DecodeConverter(Dafny.Sequence<char> s) {
      return _118_Base64_Compile.__default.DecodeRecursively(_118_Base64_Compile.__default.FromCharsToIndices(s));
    }
    public static Dafny.Sequence<char> EncodeConverter(Dafny.Sequence<byte> b) {
      return _118_Base64_Compile.__default.FromIndicesToChars(_118_Base64_Compile.__default.EncodeRecursively(b));
    }
    public static bool Is1Padding(Dafny.Sequence<char> s) {
      return ((((((new BigInteger((s).Count)) == (new BigInteger(4))) && (_118_Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.Zero)))) && (_118_Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.One)))) && (_118_Base64_Compile.__default.IsBase64Char((s).Select(new BigInteger(2))))) && (((byte)((_118_Base64_Compile.__default.Base64Inv((s).Select(new BigInteger(2)))) % (4))) == (0))) && (((s).Select(new BigInteger(3))) == ('='));
    }
    public static Dafny.Sequence<byte> Decode1Padding(Dafny.Sequence<char> s) {
      _System.Tuple4<char,char,char,char> _772_c = @_System.Tuple4<char,char,char,char>.create((s).Select(BigInteger.Zero), (s).Select(BigInteger.One), (s).Select(new BigInteger(2)), 'A');
_System.Tuple3<byte,byte,byte> _773_d = _118_Base64_Compile.__default.DecodeBlock(@_System.Tuple4<byte,byte,byte,byte>.create(_118_Base64_Compile.__default.Base64Inv((_772_c).dtor__0), _118_Base64_Compile.__default.Base64Inv((_772_c).dtor__1), _118_Base64_Compile.__default.Base64Inv((_772_c).dtor__2), _118_Base64_Compile.__default.Base64Inv((_772_c).dtor__3)));
return Dafny.Sequence<byte>.FromElements((_773_d).dtor__0, (_773_d).dtor__1);
    }
    public static Dafny.Sequence<char> Encode1Padding(Dafny.Sequence<byte> b) {
      _System.Tuple4<byte,byte,byte,byte> _774_e = _118_Base64_Compile.__default.EncodeBlock(@_System.Tuple3<byte,byte,byte>.create((b).Select(BigInteger.Zero), (b).Select(BigInteger.One), 0));
return Dafny.Sequence<char>.FromElements(_118_Base64_Compile.__default.Base64Char((_774_e).dtor__0), _118_Base64_Compile.__default.Base64Char((_774_e).dtor__1), _118_Base64_Compile.__default.Base64Char((_774_e).dtor__2), '=');
    }
    public static bool Is2Padding(Dafny.Sequence<char> s) {
      return ((((((new BigInteger((s).Count)) == (new BigInteger(4))) && (_118_Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.Zero)))) && (_118_Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.One)))) && (((byte)((_118_Base64_Compile.__default.Base64Inv((s).Select(BigInteger.One))) % (16))) == (0))) && (((s).Select(new BigInteger(2))) == ('='))) && (((s).Select(new BigInteger(3))) == ('='));
    }
    public static Dafny.Sequence<byte> Decode2Padding(Dafny.Sequence<char> s) {
      _System.Tuple4<char,char,char,char> _775_c = @_System.Tuple4<char,char,char,char>.create((s).Select(BigInteger.Zero), (s).Select(BigInteger.One), 'A', 'A');
_System.Tuple3<byte,byte,byte> _776_d = _118_Base64_Compile.__default.DecodeBlock(@_System.Tuple4<byte,byte,byte,byte>.create(_118_Base64_Compile.__default.Base64Inv((_775_c).dtor__0), _118_Base64_Compile.__default.Base64Inv((_775_c).dtor__1), _118_Base64_Compile.__default.Base64Inv((_775_c).dtor__2), _118_Base64_Compile.__default.Base64Inv((_775_c).dtor__3)));
return Dafny.Sequence<byte>.FromElements((_776_d).dtor__0);
    }
    public static Dafny.Sequence<char> Encode2Padding(Dafny.Sequence<byte> b) {
      _System.Tuple4<byte,byte,byte,byte> _777_e = _118_Base64_Compile.__default.EncodeBlock(@_System.Tuple3<byte,byte,byte>.create((b).Select(BigInteger.Zero), 0, 0));
return Dafny.Sequence<char>.FromElements(_118_Base64_Compile.__default.Base64Char((_777_e).dtor__0), _118_Base64_Compile.__default.Base64Char((_777_e).dtor__1), '=', '=');
    }
    public static bool IsBase64String(Dafny.Sequence<char> s) {
      return ((Dafny.Helpers.EuclideanModulus(new BigInteger((s).Count), new BigInteger(4))).Sign == 0) && ((_118_Base64_Compile.__default.IsUnpaddedBase64String(s)) || ((_118_Base64_Compile.__default.IsUnpaddedBase64String((s).Take((new BigInteger((s).Count)) - (new BigInteger(4))))) && ((_118_Base64_Compile.__default.Is2Padding((s).Drop((new BigInteger((s).Count)) - (new BigInteger(4))))) || (_118_Base64_Compile.__default.Is1Padding((s).Drop((new BigInteger((s).Count)) - (new BigInteger(4))))))));
    }
    public static Dafny.Sequence<byte> DecodeValid(Dafny.Sequence<char> s) {
      if ((s).Equals((Dafny.Sequence<char>.FromElements()))) {
        return Dafny.Sequence<byte>.FromElements();
      } else  {
        if (_118_Base64_Compile.__default.Is2Padding((s).Drop((new BigInteger((s).Count)) - (new BigInteger(4))))) {
          return (_118_Base64_Compile.__default.DecodeConverter((s).Take((new BigInteger((s).Count)) - (new BigInteger(4))))).Concat((_118_Base64_Compile.__default.Decode2Padding((s).Drop((new BigInteger((s).Count)) - (new BigInteger(4))))));
        } else  {
          if (_118_Base64_Compile.__default.Is1Padding((s).Drop((new BigInteger((s).Count)) - (new BigInteger(4))))) {
            return (_118_Base64_Compile.__default.DecodeConverter((s).Take((new BigInteger((s).Count)) - (new BigInteger(4))))).Concat((_118_Base64_Compile.__default.Decode1Padding((s).Drop((new BigInteger((s).Count)) - (new BigInteger(4))))));
          } else  {
            return _118_Base64_Compile.__default.DecodeConverter(s);
          }
        }
      }
    }
    public static STL.Result<Dafny.Sequence<byte>> Decode(Dafny.Sequence<char> s) {
      if (_118_Base64_Compile.__default.IsBase64String(s)) {
        return @STL.Result<Dafny.Sequence<byte>>.create_Success(_118_Base64_Compile.__default.DecodeValid(s));
      } else  {
        return @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("The encoding is malformed"));
      }
    }
    public static Dafny.Sequence<char> Encode(Dafny.Sequence<byte> b) {
      Dafny.Sequence<char> _778_res = ((Dafny.Helpers.EuclideanModulus(new BigInteger((b).Count), new BigInteger(3))).Sign == 0) ? (_118_Base64_Compile.__default.EncodeConverter(b)) : (((Dafny.Helpers.EuclideanModulus(new BigInteger((b).Count), new BigInteger(3))) == (BigInteger.One)) ? ((_118_Base64_Compile.__default.EncodeConverter((b).Take((new BigInteger((b).Count)) - (BigInteger.One)))).Concat((_118_Base64_Compile.__default.Encode2Padding((b).Drop((new BigInteger((b).Count)) - (BigInteger.One)))))) : ((_118_Base64_Compile.__default.EncodeConverter((b).Take((new BigInteger((b).Count)) - (new BigInteger(2))))).Concat((_118_Base64_Compile.__default.Encode1Padding((b).Drop((new BigInteger((b).Count)) - (new BigInteger(2))))))));
return _778_res;
    }
    public static void TestBase64(Dafny.Sequence<char> msg, Dafny.Sequence<char> expected)
    {
    TAIL_CALL_START: ;
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("The message is: "));
Dafny.Helpers.Print(msg);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.Sequence<byte> _779_uint8Msg;
      _779_uint8Msg = Dafny.Sequence<byte>.FromElements();
      BigInteger _780_i;
      _780_i = BigInteger.Zero;
      while ((_780_i) < (new BigInteger((msg).Count))) {
        _779_uint8Msg = (_779_uint8Msg).Concat((Dafny.Sequence<byte>.FromElements((byte)(new BigInteger((msg).Select(_780_i))))));
        _780_i = (_780_i) + (BigInteger.One);
      }
      Dafny.Sequence<char> _781_encoded;
      _781_encoded = _118_Base64_Compile.__default.Encode(_779_uint8Msg);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("The encoding is: "));
Dafny.Helpers.Print(_781_encoded);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("The expected is: "));
Dafny.Helpers.Print(expected);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("The encoding "));
Dafny.Helpers.Print(((_781_encoded).Equals((expected))) ? (Dafny.Sequence<char>.FromString("matches")) : (Dafny.Sequence<char>.FromString("doesn't match")));
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(" the expected.\n"));
      STL.Result<Dafny.Sequence<byte>> _782_decoded;
      _782_decoded = _118_Base64_Compile.__default.Decode(_781_encoded);
      { }
      Dafny.Sequence<char> _783_dmsg;
      _783_dmsg = Dafny.Sequence<char>.FromString("");
      _780_i = BigInteger.Zero;
      while ((_780_i) < (new BigInteger(((_782_decoded).dtor_value).Count))) {
        _783_dmsg = (_783_dmsg).Concat((Dafny.Sequence<char>.FromElements((char)(new BigInteger(((_782_decoded).dtor_value).Select(_780_i))))));
        _780_i = (_780_i) + (BigInteger.One);
      }
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("The decoded message is: "));
Dafny.Helpers.Print(_783_dmsg);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n\n"));
    }
  }
} // end of namespace _118_Base64_Compile
namespace _0_Deserialize_Compile {









  public partial class __default {
    public static STL.Result<_76_MessageHeader_Compile.Header> DeserializeHeader(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<_76_MessageHeader_Compile.Header> res = STL.Result<_76_MessageHeader_Compile.Header>.Default;
      _76_MessageHeader_Compile.HeaderBody _784_hb = _76_MessageHeader_Compile.HeaderBody.Default;
      STL.Result<_76_MessageHeader_Compile.HeaderBody> _785_valueOrError0;
STL.Result<_76_MessageHeader_Compile.HeaderBody> _out44;
var _outcollector44 = _0_Deserialize_Compile.__default.DeserializeHeaderBody(rd);
_out44 = _outcollector44;
_785_valueOrError0 = _out44;
      if ((_785_valueOrError0).IsFailure()) {
        res = (_785_valueOrError0).PropagateFailure<_76_MessageHeader_Compile.Header>();
return res;
      }
      _784_hb = (_785_valueOrError0).Extract();
      _76_MessageHeader_Compile.HeaderAuthentication _786_auth = _76_MessageHeader_Compile.HeaderAuthentication.Default;
      STL.Result<_76_MessageHeader_Compile.HeaderAuthentication> _787_valueOrError1;
STL.Result<_76_MessageHeader_Compile.HeaderAuthentication> _out45;
var _outcollector45 = _0_Deserialize_Compile.__default.DeserializeHeaderAuthentication(rd, (_784_hb).dtor_algorithmSuiteID);
_out45 = _outcollector45;
_787_valueOrError1 = _out45;
      if ((_787_valueOrError1).IsFailure()) {
        res = (_787_valueOrError1).PropagateFailure<_76_MessageHeader_Compile.Header>();
return res;
      }
      _786_auth = (_787_valueOrError1).Extract();
      res = @STL.Result<_76_MessageHeader_Compile.Header>.create_Success(@_76_MessageHeader_Compile.Header.create(_784_hb, _786_auth));
return res;
      return res;
    }
    public static STL.Result<_76_MessageHeader_Compile.HeaderBody> DeserializeHeaderBody(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<_76_MessageHeader_Compile.HeaderBody> ret = STL.Result<_76_MessageHeader_Compile.HeaderBody>.Default;
      byte _788_version = _76_MessageHeader_Compile.Version.Witness;
      STL.Result<byte> _789_valueOrError0;
STL.Result<byte> _out46;
var _outcollector46 = _0_Deserialize_Compile.__default.DeserializeVersion(rd);
_out46 = _outcollector46;
_789_valueOrError0 = _out46;
      if ((_789_valueOrError0).IsFailure()) {
        ret = (_789_valueOrError0).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _788_version = (_789_valueOrError0).Extract();
      byte _790_typ = _76_MessageHeader_Compile.Type.Witness;
      STL.Result<byte> _791_valueOrError1;
STL.Result<byte> _out47;
var _outcollector47 = _0_Deserialize_Compile.__default.DeserializeType(rd);
_out47 = _outcollector47;
_791_valueOrError1 = _out47;
      if ((_791_valueOrError1).IsFailure()) {
        ret = (_791_valueOrError1).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _790_typ = (_791_valueOrError1).Extract();
      ushort _792_algorithmSuiteID = _25_AlgorithmSuite_Compile.ID.Witness;
      STL.Result<ushort> _793_valueOrError2;
STL.Result<ushort> _out48;
var _outcollector48 = _0_Deserialize_Compile.__default.DeserializeAlgorithmSuiteID(rd);
_out48 = _outcollector48;
_793_valueOrError2 = _out48;
      if ((_793_valueOrError2).IsFailure()) {
        ret = (_793_valueOrError2).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _792_algorithmSuiteID = (_793_valueOrError2).Extract();
      Dafny.Sequence<byte> _794_messageID = _76_MessageHeader_Compile.MessageID.Witness;
      STL.Result<Dafny.Sequence<byte>> _795_valueOrError3;
STL.Result<Dafny.Sequence<byte>> _out49;
var _outcollector49 = _0_Deserialize_Compile.__default.DeserializeMsgID(rd);
_out49 = _outcollector49;
_795_valueOrError3 = _out49;
      if ((_795_valueOrError3).IsFailure()) {
        ret = (_795_valueOrError3).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _794_messageID = (_795_valueOrError3).Extract();
      Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> _796_aad = Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.Empty;
      STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _797_valueOrError4;
STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _out50;
var _outcollector50 = _0_Deserialize_Compile.__default.DeserializeAAD(rd);
_out50 = _outcollector50;
_797_valueOrError4 = _out50;
      if ((_797_valueOrError4).IsFailure()) {
        ret = (_797_valueOrError4).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _796_aad = (_797_valueOrError4).Extract();
      _76_MessageHeader_Compile.EncryptedDataKeys _798_encryptedDataKeys = _76_MessageHeader_Compile.EncryptedDataKeys.Default;
      STL.Result<_76_MessageHeader_Compile.EncryptedDataKeys> _799_valueOrError5;
STL.Result<_76_MessageHeader_Compile.EncryptedDataKeys> _out51;
var _outcollector51 = _0_Deserialize_Compile.__default.DeserializeEncryptedDataKeys(rd);
_out51 = _outcollector51;
_799_valueOrError5 = _out51;
      if ((_799_valueOrError5).IsFailure()) {
        ret = (_799_valueOrError5).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _798_encryptedDataKeys = (_799_valueOrError5).Extract();
      _76_MessageHeader_Compile.ContentType _800_contentType = _76_MessageHeader_Compile.ContentType.Default;
      STL.Result<_76_MessageHeader_Compile.ContentType> _801_valueOrError6;
STL.Result<_76_MessageHeader_Compile.ContentType> _out52;
var _outcollector52 = _0_Deserialize_Compile.__default.DeserializeContentType(rd);
_out52 = _outcollector52;
_801_valueOrError6 = _out52;
      if ((_801_valueOrError6).IsFailure()) {
        ret = (_801_valueOrError6).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _800_contentType = (_801_valueOrError6).Extract();
      Dafny.Sequence<byte> _802___v2 = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _803_valueOrError7;
STL.Result<Dafny.Sequence<byte>> _out53;
var _outcollector53 = _0_Deserialize_Compile.__default.DeserializeReserved(rd);
_out53 = _outcollector53;
_803_valueOrError7 = _out53;
      if ((_803_valueOrError7).IsFailure()) {
        ret = (_803_valueOrError7).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _802___v2 = (_803_valueOrError7).Extract();
      byte _804_ivLength = 0;
      STL.Result<byte> _805_valueOrError8;
STL.Result<byte> _out54;
var _outcollector54 = (rd).ReadByte();
_out54 = _outcollector54;
_805_valueOrError8 = _out54;
      if ((_805_valueOrError8).IsFailure()) {
        ret = (_805_valueOrError8).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _804_ivLength = (_805_valueOrError8).Extract();
      uint _806_frameLength = 0;
      STL.Result<uint> _807_valueOrError9;
STL.Result<uint> _out55;
var _outcollector55 = (rd).ReadUInt32();
_out55 = _outcollector55;
_807_valueOrError9 = _out55;
      if ((_807_valueOrError9).IsFailure()) {
        ret = (_807_valueOrError9).PropagateFailure<_76_MessageHeader_Compile.HeaderBody>();
return ret;
      }
      _806_frameLength = (_807_valueOrError9).Extract();
      if ((new BigInteger(_804_ivLength)) != (_25_AlgorithmSuite_Compile.ID.IVLength(_792_algorithmSuiteID))) {
        ret = @STL.Result<_76_MessageHeader_Compile.HeaderBody>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Incorrect IV length."));
return ret;
      }
      if (((_800_contentType).is_NonFramed) && ((_806_frameLength) != (0U))) {
        ret = @STL.Result<_76_MessageHeader_Compile.HeaderBody>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Frame length must be 0 when content type is non-framed."));
return ret;
      } else if (((_800_contentType).is_Framed) && ((_806_frameLength) == (0U))) {
        ret = @STL.Result<_76_MessageHeader_Compile.HeaderBody>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Frame length must be non-0 when content type is framed."));
return ret;
      }
      _76_MessageHeader_Compile.HeaderBody _808_hb;
      _808_hb = @_76_MessageHeader_Compile.HeaderBody.create(_788_version, _790_typ, _792_algorithmSuiteID, _794_messageID, _796_aad, _798_encryptedDataKeys, _800_contentType, _804_ivLength, _806_frameLength);
      ret = @STL.Result<_76_MessageHeader_Compile.HeaderBody>.create_Success(_808_hb);
return ret;
      return ret;
    }
    public static STL.Result<_76_MessageHeader_Compile.HeaderAuthentication> DeserializeHeaderAuthentication(_54_Streams_Compile.StringReader rd, ushort algorithmSuiteID)
    {
      STL.Result<_76_MessageHeader_Compile.HeaderAuthentication> ret = STL.Result<_76_MessageHeader_Compile.HeaderAuthentication>.Default;
      Dafny.Sequence<byte> _809_iv = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _810_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out56;
var _outcollector56 = (rd).ReadExact(_25_AlgorithmSuite_Compile.ID.IVLength(algorithmSuiteID));
_out56 = _outcollector56;
_810_valueOrError0 = _out56;
      if ((_810_valueOrError0).IsFailure()) {
        ret = (_810_valueOrError0).PropagateFailure<_76_MessageHeader_Compile.HeaderAuthentication>();
return ret;
      }
      _809_iv = (_810_valueOrError0).Extract();
      Dafny.Sequence<byte> _811_authenticationTag = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _812_valueOrError1;
STL.Result<Dafny.Sequence<byte>> _out57;
var _outcollector57 = (rd).ReadExact(_25_AlgorithmSuite_Compile.ID.TagLength(algorithmSuiteID));
_out57 = _outcollector57;
_812_valueOrError1 = _out57;
      if ((_812_valueOrError1).IsFailure()) {
        ret = (_812_valueOrError1).PropagateFailure<_76_MessageHeader_Compile.HeaderAuthentication>();
return ret;
      }
      _811_authenticationTag = (_812_valueOrError1).Extract();
      ret = @STL.Result<_76_MessageHeader_Compile.HeaderAuthentication>.create_Success(@_76_MessageHeader_Compile.HeaderAuthentication.create(_809_iv, _811_authenticationTag));
return ret;
      return ret;
    }
    public static STL.Result<byte> DeserializeVersion(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<byte> ret = STL.Result<byte>.Default;
      byte _813_version = 0;
      STL.Result<byte> _814_valueOrError0;
STL.Result<byte> _out58;
var _outcollector58 = (rd).ReadByte();
_out58 = _outcollector58;
_814_valueOrError0 = _out58;
      if ((_814_valueOrError0).IsFailure()) {
        ret = (_814_valueOrError0).PropagateFailure<byte>();
return ret;
      }
      _813_version = (_814_valueOrError0).Extract();
      if ((_813_version) == (_76_MessageHeader_Compile.__default.VERSION__1)) {
        ret = @STL.Result<byte>.create_Success(_813_version);
return ret;
      } else {
        ret = @STL.Result<byte>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Version not supported."));
return ret;
      }
      return ret;
    }
    public static STL.Result<byte> DeserializeType(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<byte> ret = STL.Result<byte>.Default;
      byte _815_typ = 0;
      STL.Result<byte> _816_valueOrError0;
STL.Result<byte> _out59;
var _outcollector59 = (rd).ReadByte();
_out59 = _outcollector59;
_816_valueOrError0 = _out59;
      if ((_816_valueOrError0).IsFailure()) {
        ret = (_816_valueOrError0).PropagateFailure<byte>();
return ret;
      }
      _815_typ = (_816_valueOrError0).Extract();
      if ((_815_typ) == (_76_MessageHeader_Compile.__default.TYPE__CUSTOMER__AED)) {
        ret = @STL.Result<byte>.create_Success(_815_typ);
return ret;
      } else {
        ret = @STL.Result<byte>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Type not supported."));
return ret;
      }
      return ret;
    }
    public static STL.Result<ushort> DeserializeAlgorithmSuiteID(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<ushort> ret = STL.Result<ushort>.Default;
      ushort _817_algorithmSuiteID = 0;
      STL.Result<ushort> _818_valueOrError0;
STL.Result<ushort> _out60;
var _outcollector60 = (rd).ReadUInt16();
_out60 = _outcollector60;
_818_valueOrError0 = _out60;
      if ((_818_valueOrError0).IsFailure()) {
        ret = (_818_valueOrError0).PropagateFailure<ushort>();
return ret;
      }
      _817_algorithmSuiteID = (_818_valueOrError0).Extract();
      if ((_25_AlgorithmSuite_Compile.__default.VALID__IDS).Contains((_817_algorithmSuiteID))) {
        ret = @STL.Result<ushort>.create_Success((ushort)(_817_algorithmSuiteID));
return ret;
      } else {
        ret = @STL.Result<ushort>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Algorithm suite not supported."));
return ret;
      }
      return ret;
    }
    public static STL.Result<Dafny.Sequence<byte>> DeserializeMsgID(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<Dafny.Sequence<byte>> ret = STL.Result<Dafny.Sequence<byte>>.Default;
      Dafny.Sequence<byte> _819_msgID = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _820_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out61;
var _outcollector61 = (rd).ReadExact(_76_MessageHeader_Compile.__default.MESSAGE__ID__LEN);
_out61 = _outcollector61;
_820_valueOrError0 = _out61;
      if ((_820_valueOrError0).IsFailure()) {
        ret = (_820_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return ret;
      }
      _819_msgID = (_820_valueOrError0).Extract();
      ret = @STL.Result<Dafny.Sequence<byte>>.create_Success(_819_msgID);
return ret;
      return ret;
    }
    public static STL.Result<Dafny.Sequence<byte>> DeserializeUTF8(_54_Streams_Compile.StringReader rd, BigInteger n)
    {
      STL.Result<Dafny.Sequence<byte>> ret = STL.Result<Dafny.Sequence<byte>>.Default;
      Dafny.Sequence<byte> _821_bytes = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _822_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out62;
var _outcollector62 = (rd).ReadExact(n);
_out62 = _outcollector62;
_822_valueOrError0 = _out62;
      if ((_822_valueOrError0).IsFailure()) {
        ret = (_822_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return ret;
      }
      _821_bytes = (_822_valueOrError0).Extract();
      if (UTF8.__default.ValidUTF8Seq(_821_bytes)) {
        ret = @STL.Result<Dafny.Sequence<byte>>.create_Success(_821_bytes);
return ret;
      } else {
        ret = @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Not a valid UTF8 string."));
return ret;
      }
      return ret;
    }
    public static STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> DeserializeAAD(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> ret = STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.Default;
      { }
      ushort _823_aadLength = 0;
      STL.Result<ushort> _824_valueOrError0;
STL.Result<ushort> _out63;
var _outcollector63 = (rd).ReadUInt16();
_out63 = _outcollector63;
_824_valueOrError0 = _out63;
      if ((_824_valueOrError0).IsFailure()) {
        ret = (_824_valueOrError0).PropagateFailure<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>();
return ret;
      }
      _823_aadLength = (_824_valueOrError0).Extract();
      if ((_823_aadLength) == (0)) {
        ret = @STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_Success(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements());
return ret;
      } else if ((_823_aadLength) < (2)) {
        ret = @STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: The number of bytes in encryption context exceeds the given length."));
return ret;
      }
      BigInteger _825_totalBytesRead;
      _825_totalBytesRead = BigInteger.Zero;
      ushort _826_kvPairsCount = 0;
      STL.Result<ushort> _827_valueOrError1;
STL.Result<ushort> _out64;
var _outcollector64 = (rd).ReadUInt16();
_out64 = _outcollector64;
_827_valueOrError1 = _out64;
      if ((_827_valueOrError1).IsFailure()) {
        ret = (_827_valueOrError1).PropagateFailure<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>();
return ret;
      }
      _826_kvPairsCount = (_827_valueOrError1).Extract();
      _825_totalBytesRead = (_825_totalBytesRead) + (new BigInteger(2));
      if ((_826_kvPairsCount) == (0)) {
        ret = @STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Key value pairs count is 0."));
return ret;
      }
      Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> _828_kvPairs;
      _828_kvPairs = Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements();
      ushort _829_i;
      _829_i = 0;
      while ((_829_i) < (_826_kvPairsCount)) {
        ushort _830_keyLength = 0;
        STL.Result<ushort> _831_valueOrError2;
STL.Result<ushort> _out65;
var _outcollector65 = (rd).ReadUInt16();
_out65 = _outcollector65;
_831_valueOrError2 = _out65;
        if ((_831_valueOrError2).IsFailure()) {
          ret = (_831_valueOrError2).PropagateFailure<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>();
return ret;
        }
        _830_keyLength = (_831_valueOrError2).Extract();
        _825_totalBytesRead = (_825_totalBytesRead) + (new BigInteger(2));
        Dafny.Sequence<byte> _832_key = Dafny.Sequence<byte>.Empty;
        STL.Result<Dafny.Sequence<byte>> _833_valueOrError3;
STL.Result<Dafny.Sequence<byte>> _out66;
var _outcollector66 = _0_Deserialize_Compile.__default.DeserializeUTF8(rd, new BigInteger(_830_keyLength));
_out66 = _outcollector66;
_833_valueOrError3 = _out66;
        if ((_833_valueOrError3).IsFailure()) {
          ret = (_833_valueOrError3).PropagateFailure<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>();
return ret;
        }
        _832_key = (_833_valueOrError3).Extract();
        _825_totalBytesRead = (_825_totalBytesRead) + (new BigInteger((_832_key).Count));
        ushort _834_valueLength = 0;
        STL.Result<ushort> _835_valueOrError4;
STL.Result<ushort> _out67;
var _outcollector67 = (rd).ReadUInt16();
_out67 = _outcollector67;
_835_valueOrError4 = _out67;
        if ((_835_valueOrError4).IsFailure()) {
          ret = (_835_valueOrError4).PropagateFailure<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>();
return ret;
        }
        _834_valueLength = (_835_valueOrError4).Extract();
        _825_totalBytesRead = (_825_totalBytesRead) + (new BigInteger(2));
        if ((new BigInteger(_823_aadLength)) < ((_825_totalBytesRead) + (new BigInteger(_834_valueLength)))) {
          ret = @STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: The number of bytes in encryption context exceeds the given length."));
return ret;
        }
        Dafny.Sequence<byte> _836_value = Dafny.Sequence<byte>.Empty;
        STL.Result<Dafny.Sequence<byte>> _837_valueOrError5;
STL.Result<Dafny.Sequence<byte>> _out68;
var _outcollector68 = _0_Deserialize_Compile.__default.DeserializeUTF8(rd, new BigInteger(_834_valueLength));
_out68 = _outcollector68;
_837_valueOrError5 = _out68;
        if ((_837_valueOrError5).IsFailure()) {
          ret = (_837_valueOrError5).PropagateFailure<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>();
return ret;
        }
        _836_value = (_837_valueOrError5).Extract();
        _825_totalBytesRead = (_825_totalBytesRead) + (new BigInteger((_836_value).Count));
        STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _838_opt;
STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _out69;
var _outcollector69 = _0_Deserialize_Compile.__default.InsertNewEntry(_828_kvPairs, _832_key, _836_value);
_out69 = _outcollector69;
_838_opt = _out69;
        STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _source9 = _838_opt;
if (_source9.is_Some) {
          Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> _839_kvPairs__ = ((STL.Option_Some<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>)_source9).@get;
          { }
          _828_kvPairs = _839_kvPairs__;
        } else {
          ret = @STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Duplicate key."));
return ret;
        }
        _829_i = (ushort)((_829_i) + (1));
      }
      if ((new BigInteger(_823_aadLength)) != (_825_totalBytesRead)) {
        ret = @STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Bytes actually read differs from bytes supposed to be read."));
return ret;
      }
      ret = @STL.Result<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_Success(_828_kvPairs);
return ret;
      return ret;
    }
    public static STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> InsertNewEntry(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> kvPairs, Dafny.Sequence<byte> key, Dafny.Sequence<byte> @value)
    {
    TAIL_CALL_START: ;
STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> res = STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.Default;
      BigInteger _840_n;
      _840_n = new BigInteger((kvPairs).Count);
      while (((_840_n).Sign == 1) && (STL.__default.LexicographicLessOrEqual<byte>(key, ((kvPairs).Select((_840_n) - (BigInteger.One))).dtor__0, STL.__default.UInt8Less))) {
        _840_n = (_840_n) - (BigInteger.One);
      }
      if (((_840_n).Sign == 1) && ((((kvPairs).Select((_840_n) - (BigInteger.One))).dtor__0).Equals((key)))) {
        STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _rhs6 = @STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_None();
res = _rhs6;
return res;
      } else {
        Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> _841_kvPairs_k;
        _841_kvPairs_k = (((kvPairs).Take(_840_n)).Concat((Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>.FromElements(@_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>.create(key, @value))))).Concat(((kvPairs).Drop(_840_n)));
        { }
        STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _rhs7 = @STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.create_Some(_841_kvPairs_k);
res = _rhs7;
return res;
      }
      return res;
    }
    public static STL.Result<_76_MessageHeader_Compile.EncryptedDataKeys> DeserializeEncryptedDataKeys(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<_76_MessageHeader_Compile.EncryptedDataKeys> ret = STL.Result<_76_MessageHeader_Compile.EncryptedDataKeys>.Default;
      ushort _842_edkCount = 0;
      STL.Result<ushort> _843_valueOrError0;
STL.Result<ushort> _out70;
var _outcollector70 = (rd).ReadUInt16();
_out70 = _outcollector70;
_843_valueOrError0 = _out70;
      if ((_843_valueOrError0).IsFailure()) {
        ret = (_843_valueOrError0).PropagateFailure<_76_MessageHeader_Compile.EncryptedDataKeys>();
return ret;
      }
      _842_edkCount = (_843_valueOrError0).Extract();
      if ((_842_edkCount) == (0)) {
        ret = @STL.Result<_76_MessageHeader_Compile.EncryptedDataKeys>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Encrypted data key count is 0."));
return ret;
      }
      Dafny.Sequence<Materials.EncryptedDataKey> _844_edkEntries;
      _844_edkEntries = Dafny.Sequence<Materials.EncryptedDataKey>.FromElements();
      ushort _845_i;
      _845_i = 0;
      while ((_845_i) < (_842_edkCount)) {
        ushort _846_keyProviderIDLength = 0;
        STL.Result<ushort> _847_valueOrError1;
STL.Result<ushort> _out71;
var _outcollector71 = (rd).ReadUInt16();
_out71 = _outcollector71;
_847_valueOrError1 = _out71;
        if ((_847_valueOrError1).IsFailure()) {
          ret = (_847_valueOrError1).PropagateFailure<_76_MessageHeader_Compile.EncryptedDataKeys>();
return ret;
        }
        _846_keyProviderIDLength = (_847_valueOrError1).Extract();
        Dafny.Sequence<byte> _848_str = Dafny.Sequence<byte>.Empty;
        STL.Result<Dafny.Sequence<byte>> _849_valueOrError2;
STL.Result<Dafny.Sequence<byte>> _out72;
var _outcollector72 = _0_Deserialize_Compile.__default.DeserializeUTF8(rd, new BigInteger(_846_keyProviderIDLength));
_out72 = _outcollector72;
_849_valueOrError2 = _out72;
        if ((_849_valueOrError2).IsFailure()) {
          ret = (_849_valueOrError2).PropagateFailure<_76_MessageHeader_Compile.EncryptedDataKeys>();
return ret;
        }
        _848_str = (_849_valueOrError2).Extract();
        Dafny.Sequence<byte> _850_keyProviderID;
        _850_keyProviderID = _848_str;
        ushort _851_keyProviderInfoLength = 0;
        STL.Result<ushort> _852_valueOrError3;
STL.Result<ushort> _out73;
var _outcollector73 = (rd).ReadUInt16();
_out73 = _outcollector73;
_852_valueOrError3 = _out73;
        if ((_852_valueOrError3).IsFailure()) {
          ret = (_852_valueOrError3).PropagateFailure<_76_MessageHeader_Compile.EncryptedDataKeys>();
return ret;
        }
        _851_keyProviderInfoLength = (_852_valueOrError3).Extract();
        Dafny.Sequence<byte> _853_keyProviderInfo = Dafny.Sequence<byte>.Empty;
        STL.Result<Dafny.Sequence<byte>> _854_valueOrError4;
STL.Result<Dafny.Sequence<byte>> _out74;
var _outcollector74 = (rd).ReadExact(new BigInteger(_851_keyProviderInfoLength));
_out74 = _outcollector74;
_854_valueOrError4 = _out74;
        if ((_854_valueOrError4).IsFailure()) {
          ret = (_854_valueOrError4).PropagateFailure<_76_MessageHeader_Compile.EncryptedDataKeys>();
return ret;
        }
        _853_keyProviderInfo = (_854_valueOrError4).Extract();
        ushort _855_edkLength = 0;
        STL.Result<ushort> _856_valueOrError5;
STL.Result<ushort> _out75;
var _outcollector75 = (rd).ReadUInt16();
_out75 = _outcollector75;
_856_valueOrError5 = _out75;
        if ((_856_valueOrError5).IsFailure()) {
          ret = (_856_valueOrError5).PropagateFailure<_76_MessageHeader_Compile.EncryptedDataKeys>();
return ret;
        }
        _855_edkLength = (_856_valueOrError5).Extract();
        Dafny.Sequence<byte> _857_edk = Dafny.Sequence<byte>.Empty;
        STL.Result<Dafny.Sequence<byte>> _858_valueOrError6;
STL.Result<Dafny.Sequence<byte>> _out76;
var _outcollector76 = (rd).ReadExact(new BigInteger(_855_edkLength));
_out76 = _outcollector76;
_858_valueOrError6 = _out76;
        if ((_858_valueOrError6).IsFailure()) {
          ret = (_858_valueOrError6).PropagateFailure<_76_MessageHeader_Compile.EncryptedDataKeys>();
return ret;
        }
        _857_edk = (_858_valueOrError6).Extract();
        _844_edkEntries = (_844_edkEntries).Concat((Dafny.Sequence<Materials.EncryptedDataKey>.FromElements(@Materials.EncryptedDataKey.create(_850_keyProviderID, _853_keyProviderInfo, _857_edk))));
        _845_i = (ushort)((_845_i) + (1));
      }
      _76_MessageHeader_Compile.EncryptedDataKeys _859_edks;
      _859_edks = @_76_MessageHeader_Compile.EncryptedDataKeys.create(_844_edkEntries);
      ret = @STL.Result<_76_MessageHeader_Compile.EncryptedDataKeys>.create_Success(_859_edks);
return ret;
      return ret;
    }
    public static STL.Result<_76_MessageHeader_Compile.ContentType> DeserializeContentType(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<_76_MessageHeader_Compile.ContentType> ret = STL.Result<_76_MessageHeader_Compile.ContentType>.Default;
      byte _860_byte = 0;
      STL.Result<byte> _861_valueOrError0;
STL.Result<byte> _out77;
var _outcollector77 = (rd).ReadByte();
_out77 = _outcollector77;
_861_valueOrError0 = _out77;
      if ((_861_valueOrError0).IsFailure()) {
        ret = (_861_valueOrError0).PropagateFailure<_76_MessageHeader_Compile.ContentType>();
return ret;
      }
      _860_byte = (_861_valueOrError0).Extract();
      STL.Option<_76_MessageHeader_Compile.ContentType> _source10 = _76_MessageHeader_Compile.__default.UInt8ToContentType(_860_byte);
if (_source10.is_None) {
        ret = @STL.Result<_76_MessageHeader_Compile.ContentType>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Content type not supported."));
return ret;
      } else {
        _76_MessageHeader_Compile.ContentType _862_contentType = ((STL.Option_Some<_76_MessageHeader_Compile.ContentType>)_source10).@get;
        ret = @STL.Result<_76_MessageHeader_Compile.ContentType>.create_Success(_862_contentType);
return ret;
      }
      return ret;
    }
    public static STL.Result<Dafny.Sequence<byte>> DeserializeReserved(_54_Streams_Compile.StringReader rd)
    {
      STL.Result<Dafny.Sequence<byte>> ret = STL.Result<Dafny.Sequence<byte>>.Default;
      Dafny.Sequence<byte> _863_reserved = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _864_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out78;
var _outcollector78 = (rd).ReadExact(new BigInteger(4));
_out78 = _outcollector78;
_864_valueOrError0 = _out78;
      if ((_864_valueOrError0).IsFailure()) {
        ret = (_864_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return ret;
      }
      _863_reserved = (_864_valueOrError0).Extract();
      if ((_863_reserved).Equals((_76_MessageHeader_Compile.__default.Reserved))) {
        ret = @STL.Result<Dafny.Sequence<byte>>.create_Success(_863_reserved);
return ret;
      } else {
        ret = @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("Deserialization Error: Reserved fields must be 0."));
return ret;
      }
      return ret;
    }
  }
} // end of namespace _0_Deserialize_Compile
namespace _132_DefaultCMMDef_Compile {












  public partial class DefaultCMM : _111_CMMDefs_Compile.CMM {
    public void OfKeyring(_36_KeyringDefs_Compile.Keyring k)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this)._kr = k;
      { }
    }
    public STL.Result<Materials.EncryptionMaterials> GetEncryptionMaterials(Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> ec, STL.Option<ushort> alg__id, STL.Option<BigInteger> pt__len)
    {
      STL.Result<Materials.EncryptionMaterials> res = STL.Result<Materials.EncryptionMaterials>.Default;
      ushort _865_id;
      _865_id = ((alg__id).is_Some) ? ((alg__id).dtor_get) : (_25_AlgorithmSuite_Compile.__default.AES__256__GCM__IV12__TAG16__HKDF__SHA384__ECDSA__P384);
      STL.Option<Dafny.Sequence<byte>> _866_enc__sk;
      _866_enc__sk = @STL.Option<Dafny.Sequence<byte>>.create_None();
      Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> _867_enc__ctx;
      _867_enc__ctx = ec;
      STL.Option<Signature.ECDSAParams> _source11 = _25_AlgorithmSuite_Compile.ID.SignatureType(_865_id);
if (_source11.is_None) {
      } else {
        Signature.ECDSAParams _868_param = ((STL.Option_Some<Signature.ECDSAParams>)_source11).@get;
        STL.Option<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> _869_oab;
STL.Option<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> _out79;
var _outcollector79 = Signature.ECDSA.KeyGen(_868_param);
_out79 = _outcollector79;
_869_oab = _out79;
        STL.Option<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> _source12 = _869_oab;
if (_source12.is_None) {
          res = @STL.Result<Materials.EncryptionMaterials>.create_Failure(Dafny.Sequence<char>.FromString("Keygen error"));
return res;
        } else {
          _System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _870_ab = ((STL.Option_Some<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>)_source12).@get;
          _866_enc__sk = @STL.Option<Dafny.Sequence<byte>>.create_Some((_870_ab).dtor__1);
          Dafny.Sequence<byte> _871_enc__vk = UTF8.ValidUTF8Bytes.Witness;
          STL.Result<Dafny.Sequence<byte>> _872_valueOrError0;
          _872_valueOrError0 = UTF8.__default.Encode(_118_Base64_Compile.__default.Encode((_870_ab).dtor__0));
          if ((_872_valueOrError0).IsFailure()) {
            res = (_872_valueOrError0).PropagateFailure<Materials.EncryptionMaterials>();
return res;
          }
          _871_enc__vk = (_872_valueOrError0).Extract();
          Dafny.Sequence<byte> _873_reservedField;
          _873_reservedField = Materials.__default.EC__PUBLIC__KEY__FIELD;
          { }
          { }
          { }
          STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _874_optionResult = STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>>.Default;
          { }
          STL.Option<Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>>> _out80;
var _outcollector80 = _0_Deserialize_Compile.__default.InsertNewEntry(_867_enc__ctx, _873_reservedField, _871_enc__vk);
_out80 = _outcollector80;
_874_optionResult = _out80;
          _867_enc__ctx = (_874_optionResult).dtor_get;
        }
      }
      { }
      STL.Option<Materials.DataKeyMaterials> _875_dataKeyMaterials = STL.Option<Materials.DataKeyMaterials>.Default;
      STL.Result<STL.Option<Materials.DataKeyMaterials>> _876_valueOrError1;
STL.Result<STL.Option<Materials.DataKeyMaterials>> _out81;
var _outcollector81 = ((this).kr).OnEncrypt(_865_id, _867_enc__ctx, @STL.Option<Dafny.Sequence<byte>>.create_None());
_out81 = _outcollector81;
_876_valueOrError1 = _out81;
      if ((_876_valueOrError1).IsFailure()) {
        res = (_876_valueOrError1).PropagateFailure<Materials.EncryptionMaterials>();
return res;
      }
      _875_dataKeyMaterials = (_876_valueOrError1).Extract();
      if (((_875_dataKeyMaterials).is_None) || ((new BigInteger((((_875_dataKeyMaterials).dtor_get).dtor_encryptedDataKeys).Count)).Sign == 0)) {
        res = @STL.Result<Materials.EncryptionMaterials>.create_Failure(Dafny.Sequence<char>.FromString("Could not retrieve materials required for encryption"));
return res;
      }
      res = @STL.Result<Materials.EncryptionMaterials>.create_Success(@Materials.EncryptionMaterials.create(_867_enc__ctx, (_875_dataKeyMaterials).dtor_get, _866_enc__sk));
return res;
      return res;
    }
    public STL.Result<Materials.DecryptionMaterials> DecryptMaterials(ushort alg__id, Dafny.Sequence<Materials.EncryptedDataKey> edks, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> enc__ctx)
    {
      STL.Result<Materials.DecryptionMaterials> res = STL.Result<Materials.DecryptionMaterials>.Default;
      STL.Option<Dafny.Sequence<byte>> _877_vkey;
      _877_vkey = @STL.Option<Dafny.Sequence<byte>>.create_None();
      if ((_25_AlgorithmSuite_Compile.ID.SignatureType(alg__id)).is_Some) {
        Dafny.Sequence<byte> _878_reservedField;
        _878_reservedField = Materials.__default.EC__PUBLIC__KEY__FIELD;
        STL.Option<Dafny.Sequence<byte>> _879_encodedVKey;
        _879_encodedVKey = Materials.__default.EncCtxLookup(enc__ctx, _878_reservedField);
        if ((_879_encodedVKey).Equals((@STL.Option<Dafny.Sequence<byte>>.create_None()))) {
          res = @STL.Result<Materials.DecryptionMaterials>.create_Failure(Dafny.Sequence<char>.FromString("Could not get materials required for decryption."));
return res;
        }
        Dafny.Sequence<char> _880_utf8Decoded = Dafny.Sequence<char>.Empty;
        STL.Result<Dafny.Sequence<char>> _881_valueOrError0;
        _881_valueOrError0 = UTF8.__default.Decode((_879_encodedVKey).dtor_get);
        if ((_881_valueOrError0).IsFailure()) {
          res = (_881_valueOrError0).PropagateFailure<Materials.DecryptionMaterials>();
return res;
        }
        _880_utf8Decoded = (_881_valueOrError0).Extract();
        Dafny.Sequence<byte> _882_base64Decoded = Dafny.Sequence<byte>.Empty;
        STL.Result<Dafny.Sequence<byte>> _883_valueOrError1;
        _883_valueOrError1 = _118_Base64_Compile.__default.Decode(_880_utf8Decoded);
        if ((_883_valueOrError1).IsFailure()) {
          res = (_883_valueOrError1).PropagateFailure<Materials.DecryptionMaterials>();
return res;
        }
        _882_base64Decoded = (_883_valueOrError1).Extract();
        _877_vkey = @STL.Option<Dafny.Sequence<byte>>.create_Some(_882_base64Decoded);
      }
      STL.Option<Materials.OnDecryptResult> _884_onDecryptResult = STL.Option<Materials.OnDecryptResult>.Default;
      STL.Result<STL.Option<Materials.OnDecryptResult>> _885_valueOrError2;
STL.Result<STL.Option<Materials.OnDecryptResult>> _out82;
var _outcollector82 = ((this).kr).OnDecrypt(alg__id, enc__ctx, edks);
_out82 = _outcollector82;
_885_valueOrError2 = _out82;
      if ((_885_valueOrError2).IsFailure()) {
        res = (_885_valueOrError2).PropagateFailure<Materials.DecryptionMaterials>();
return res;
      }
      _884_onDecryptResult = (_885_valueOrError2).Extract();
      if ((_884_onDecryptResult).is_None) {
        res = @STL.Result<Materials.DecryptionMaterials>.create_Failure(Dafny.Sequence<char>.FromString("Keyring.OnDecrypt did not return a value."));
return res;
      }
      res = @STL.Result<Materials.DecryptionMaterials>.create_Success(@Materials.DecryptionMaterials.create(alg__id, enc__ctx, ((_884_onDecryptResult).dtor_get).dtor_plaintextDataKey, _877_vkey, ((_884_onDecryptResult).dtor_get).dtor_keyringTrace));
return res;
      return res;
    }
    public _36_KeyringDefs_Compile.Keyring _kr = default(_36_KeyringDefs_Compile.Keyring);
public _36_KeyringDefs_Compile.Keyring kr { get {
      return this._kr;
    } }
  }

} // end of namespace _132_DefaultCMMDef_Compile
namespace _0_MessageBody_Compile {











  public partial class __default {
    public static STL.Result<Dafny.Sequence<byte>> EncryptMessageBody(Dafny.Sequence<byte> plaintext, BigInteger frameLength, Dafny.Sequence<byte> messageID, Dafny.Sequence<byte> key, ushort algorithmSuiteID)
    {
      STL.Result<Dafny.Sequence<byte>> res = STL.Result<Dafny.Sequence<byte>>.Default;
      Dafny.Sequence<byte> _886_body;
      _886_body = Dafny.Sequence<byte>.FromElements();
      BigInteger _887_n;
uint _888_sequenceNumber;
      BigInteger _rhs8 = BigInteger.Zero;
uint _rhs9 = _0_MessageBody_Compile.__default.START__SEQUENCE__NUMBER;
_887_n = _rhs8;
_888_sequenceNumber = _rhs9;
      while (((_887_n) + (frameLength)) < (new BigInteger((plaintext).Count))) {
        if ((_888_sequenceNumber) == (_0_MessageBody_Compile.__default.ENDFRAME__SEQUENCE__NUMBER)) {
          res = @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("too many frames"));
return res;
        }
        Dafny.Sequence<byte> _889_plaintextFrame;
        _889_plaintextFrame = (plaintext).Subsequence(_887_n, (_887_n) + (frameLength));
        Dafny.Sequence<byte> _890_regularFrame = Dafny.Sequence<byte>.Empty;
        STL.Result<Dafny.Sequence<byte>> _891_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out83;
var _outcollector83 = _0_MessageBody_Compile.__default.EncryptRegularFrame(algorithmSuiteID, key, messageID, _889_plaintextFrame, _888_sequenceNumber);
_out83 = _outcollector83;
_891_valueOrError0 = _out83;
        if ((_891_valueOrError0).IsFailure()) {
          res = (_891_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return res;
        }
        _890_regularFrame = (_891_valueOrError0).Extract();
        _886_body = (_886_body).Concat((_890_regularFrame));
        BigInteger _rhs10 = (_887_n) + (frameLength);
uint _rhs11 = (_888_sequenceNumber) + (1U);
_887_n = _rhs10;
_888_sequenceNumber = _rhs11;
      }
      Dafny.Sequence<byte> _892_finalFrame = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _893_valueOrError1;
STL.Result<Dafny.Sequence<byte>> _out84;
var _outcollector84 = _0_MessageBody_Compile.__default.EncryptFinalFrame(algorithmSuiteID, key, frameLength, messageID, (plaintext).Drop(_887_n), _888_sequenceNumber);
_out84 = _outcollector84;
_893_valueOrError1 = _out84;
      if ((_893_valueOrError1).IsFailure()) {
        res = (_893_valueOrError1).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _892_finalFrame = (_893_valueOrError1).Extract();
      _886_body = (_886_body).Concat((_892_finalFrame));
      res = @STL.Result<Dafny.Sequence<byte>>.create_Success(_886_body);
return res;
      return res;
    }
    public static STL.Result<Dafny.Sequence<byte>> EncryptRegularFrame(ushort algorithmSuiteID, Dafny.Sequence<byte> key, Dafny.Sequence<byte> messageID, Dafny.Sequence<byte> plaintext, uint sequenceNumber)
    {
      STL.Result<Dafny.Sequence<byte>> res = STL.Result<Dafny.Sequence<byte>>.Default;
      Dafny.Sequence<byte> _894_seqNumSeq;
      _894_seqNumSeq = STLUInt.__default.UInt32ToSeq(sequenceNumber);
      Dafny.Sequence<byte> _895_unauthenticatedFrame;
      _895_unauthenticatedFrame = _894_seqNumSeq;
      Dafny.Sequence<byte> _896_iv;
      _896_iv = (((System.Func<Dafny.Sequence<byte>>) (() => {
        BigInteger dim8 = (_25_AlgorithmSuite_Compile.ID.IVLength(algorithmSuiteID)) - (new BigInteger(4));
var arr8 = new byte[(int)(dim8)];
for (int i8 = 0; i8 < dim8; i8++) { 
          var _897___v0 = (BigInteger) i8;
arr8[(int)(_897___v0)] = 0;
        }
        return Dafny.Sequence<byte>.FromArray(arr8);
      }))()).Concat((STLUInt.__default.UInt32ToSeq(sequenceNumber)));
      { }
      _895_unauthenticatedFrame = (_895_unauthenticatedFrame).Concat((_896_iv));
      Dafny.Sequence<byte> _898_aad;
Dafny.Sequence<byte> _out85;
var _outcollector85 = _0_MessageBody_Compile.__default.BodyAAD(messageID, false, sequenceNumber, (ulong)(plaintext).LongCount);
_out85 = _outcollector85;
_898_aad = _out85;
      AESEncryption.EncryptionOutput _899_encryptionOutput = AESEncryption.EncryptionOutput.Default;
      STL.Result<AESEncryption.EncryptionOutput> _900_valueOrError0;
STL.Result<AESEncryption.EncryptionOutput> _out86;
var _outcollector86 = AESEncryption.AES_GCM.AESEncrypt(_25_AlgorithmSuite_Compile.ID.EncryptionSuite(algorithmSuiteID), _896_iv, key, plaintext, _898_aad);
_out86 = _outcollector86;
_900_valueOrError0 = _out86;
      if ((_900_valueOrError0).IsFailure()) {
        res = (_900_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _899_encryptionOutput = (_900_valueOrError0).Extract();
      _895_unauthenticatedFrame = ((_895_unauthenticatedFrame).Concat(((_899_encryptionOutput).dtor_cipherText))).Concat(((_899_encryptionOutput).dtor_authTag));
      res = @STL.Result<Dafny.Sequence<byte>>.create_Success(_895_unauthenticatedFrame);
return res;
      return res;
    }
    public static STL.Result<Dafny.Sequence<byte>> EncryptFinalFrame(ushort algorithmSuiteID, Dafny.Sequence<byte> key, BigInteger frameLength, Dafny.Sequence<byte> messageID, Dafny.Sequence<byte> plaintext, uint sequenceNumber)
    {
      STL.Result<Dafny.Sequence<byte>> res = STL.Result<Dafny.Sequence<byte>>.Default;
      Dafny.Sequence<byte> _901_unauthenticatedFrame;
      _901_unauthenticatedFrame = STLUInt.__default.UInt32ToSeq(_0_MessageBody_Compile.__default.ENDFRAME__SEQUENCE__NUMBER);
      Dafny.Sequence<byte> _902_seqNumSeq;
      _902_seqNumSeq = STLUInt.__default.UInt32ToSeq(sequenceNumber);
      _901_unauthenticatedFrame = (_901_unauthenticatedFrame).Concat((_902_seqNumSeq));
      Dafny.Sequence<byte> _903_iv;
      _903_iv = (((System.Func<Dafny.Sequence<byte>>) (() => {
        BigInteger dim9 = (_25_AlgorithmSuite_Compile.ID.IVLength(algorithmSuiteID)) - (new BigInteger(4));
var arr9 = new byte[(int)(dim9)];
for (int i9 = 0; i9 < dim9; i9++) { 
          var _904___v1 = (BigInteger) i9;
arr9[(int)(_904___v1)] = 0;
        }
        return Dafny.Sequence<byte>.FromArray(arr9);
      }))()).Concat((STLUInt.__default.UInt32ToSeq(sequenceNumber)));
      { }
      _901_unauthenticatedFrame = (_901_unauthenticatedFrame).Concat((_903_iv));
      _901_unauthenticatedFrame = (_901_unauthenticatedFrame).Concat((STLUInt.__default.UInt32ToSeq((uint)(plaintext).LongCount)));
      Dafny.Sequence<byte> _905_aad;
Dafny.Sequence<byte> _out87;
var _outcollector87 = _0_MessageBody_Compile.__default.BodyAAD(messageID, true, sequenceNumber, (ulong)(plaintext).LongCount);
_out87 = _outcollector87;
_905_aad = _out87;
      AESEncryption.EncryptionOutput _906_encryptionOutput = AESEncryption.EncryptionOutput.Default;
      STL.Result<AESEncryption.EncryptionOutput> _907_valueOrError0;
STL.Result<AESEncryption.EncryptionOutput> _out88;
var _outcollector88 = AESEncryption.AES_GCM.AESEncrypt(_25_AlgorithmSuite_Compile.ID.EncryptionSuite(algorithmSuiteID), _903_iv, key, plaintext, _905_aad);
_out88 = _outcollector88;
_907_valueOrError0 = _out88;
      if ((_907_valueOrError0).IsFailure()) {
        res = (_907_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _906_encryptionOutput = (_907_valueOrError0).Extract();
      _901_unauthenticatedFrame = ((_901_unauthenticatedFrame).Concat(((_906_encryptionOutput).dtor_cipherText))).Concat(((_906_encryptionOutput).dtor_authTag));
      res = @STL.Result<Dafny.Sequence<byte>>.create_Success(_901_unauthenticatedFrame);
return res;
      return res;
    }
    public static STL.Result<Dafny.Sequence<byte>> DecryptFramedMessageBody(_54_Streams_Compile.StringReader rd, ushort algorithmSuiteID, Dafny.Sequence<byte> key, BigInteger frameLength, Dafny.Sequence<byte> messageID)
    {
      STL.Result<Dafny.Sequence<byte>> res = STL.Result<Dafny.Sequence<byte>>.Default;
      Dafny.Sequence<byte> _908_plaintext;
      _908_plaintext = Dafny.Sequence<byte>.FromElements();
      uint _909_n;
      _909_n = 1U;
      while (true) {
        _System.Tuple2<Dafny.Sequence<byte>,bool> _910_pair = _System.Tuple2<Dafny.Sequence<byte>,bool>.Default;
        STL.Result<_System.Tuple2<Dafny.Sequence<byte>,bool>> _911_valueOrError0;
STL.Result<_System.Tuple2<Dafny.Sequence<byte>,bool>> _out89;
var _outcollector89 = _0_MessageBody_Compile.__default.DecryptFrame(rd, algorithmSuiteID, key, frameLength, messageID, _909_n);
_out89 = _outcollector89;
_911_valueOrError0 = _out89;
        if ((_911_valueOrError0).IsFailure()) {
          res = (_911_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return res;
        }
        _910_pair = (_911_valueOrError0).Extract();
        _System.Tuple2<Dafny.Sequence<byte>,bool> _let_tmp_rhs0 = _910_pair;
Dafny.Sequence<byte> _912_framePlaintext = ((_System.Tuple2<Dafny.Sequence<byte>,bool>)_let_tmp_rhs0)._0;
bool _913_final = ((_System.Tuple2<Dafny.Sequence<byte>,bool>)_let_tmp_rhs0)._1;
        _908_plaintext = (_908_plaintext).Concat((_912_framePlaintext));
        if (_913_final) {
          goto after_0;
        }
        _909_n = (_909_n) + (1U);
      }
    after_0: ;
      res = @STL.Result<Dafny.Sequence<byte>>.create_Success(_908_plaintext);
return res;
      return res;
    }
    public static STL.Result<_System.Tuple2<Dafny.Sequence<byte>,bool>> DecryptFrame(_54_Streams_Compile.StringReader rd, ushort algorithmSuiteID, Dafny.Sequence<byte> key, BigInteger frameLength, Dafny.Sequence<byte> messageID, uint expectedSequenceNumber)
    {
      STL.Result<_System.Tuple2<Dafny.Sequence<byte>,bool>> res = STL.Result<_System.Tuple2<Dafny.Sequence<byte>,bool>>.Default;
      bool _914_final;
      _914_final = false;
      uint _915_sequenceNumber = 0;
      STL.Result<uint> _916_valueOrError0;
STL.Result<uint> _out90;
var _outcollector90 = (rd).ReadUInt32();
_out90 = _outcollector90;
_916_valueOrError0 = _out90;
      if ((_916_valueOrError0).IsFailure()) {
        res = (_916_valueOrError0).PropagateFailure<_System.Tuple2<Dafny.Sequence<byte>,bool>>();
return res;
      }
      _915_sequenceNumber = (_916_valueOrError0).Extract();
      if ((_915_sequenceNumber) == (_0_MessageBody_Compile.__default.ENDFRAME__SEQUENCE__NUMBER)) {
        _914_final = true;
        STL.Result<uint> _917_valueOrError1;
STL.Result<uint> _out91;
var _outcollector91 = (rd).ReadUInt32();
_out91 = _outcollector91;
_917_valueOrError1 = _out91;
        if ((_917_valueOrError1).IsFailure()) {
          res = (_917_valueOrError1).PropagateFailure<_System.Tuple2<Dafny.Sequence<byte>,bool>>();
return res;
        }
        _915_sequenceNumber = (_917_valueOrError1).Extract();
      }
      if ((_915_sequenceNumber) != (expectedSequenceNumber)) {
        res = @STL.Result<_System.Tuple2<Dafny.Sequence<byte>,bool>>.create_Failure(Dafny.Sequence<char>.FromString("unexpected frame sequence number"));
return res;
      }
      Dafny.Sequence<byte> _918_iv = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _919_valueOrError2;
STL.Result<Dafny.Sequence<byte>> _out92;
var _outcollector92 = (rd).ReadExact(_25_AlgorithmSuite_Compile.ID.IVLength(algorithmSuiteID));
_out92 = _outcollector92;
_919_valueOrError2 = _out92;
      if ((_919_valueOrError2).IsFailure()) {
        res = (_919_valueOrError2).PropagateFailure<_System.Tuple2<Dafny.Sequence<byte>,bool>>();
return res;
      }
      _918_iv = (_919_valueOrError2).Extract();
      uint _920_len;
      _920_len = (uint)(frameLength);
      if (_914_final) {
        STL.Result<uint> _921_valueOrError3;
STL.Result<uint> _out93;
var _outcollector93 = (rd).ReadUInt32();
_out93 = _outcollector93;
_921_valueOrError3 = _out93;
        if ((_921_valueOrError3).IsFailure()) {
          res = (_921_valueOrError3).PropagateFailure<_System.Tuple2<Dafny.Sequence<byte>,bool>>();
return res;
        }
        _920_len = (_921_valueOrError3).Extract();
      }
      Dafny.Sequence<byte> _922_aad;
Dafny.Sequence<byte> _out94;
var _outcollector94 = _0_MessageBody_Compile.__default.BodyAAD(messageID, _914_final, _915_sequenceNumber, (ulong)(_920_len));
_out94 = _outcollector94;
_922_aad = _out94;
      Dafny.Sequence<byte> _923_ciphertext = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _924_valueOrError4;
STL.Result<Dafny.Sequence<byte>> _out95;
var _outcollector95 = (rd).ReadExact(new BigInteger(_920_len));
_out95 = _outcollector95;
_924_valueOrError4 = _out95;
      if ((_924_valueOrError4).IsFailure()) {
        res = (_924_valueOrError4).PropagateFailure<_System.Tuple2<Dafny.Sequence<byte>,bool>>();
return res;
      }
      _923_ciphertext = (_924_valueOrError4).Extract();
      Dafny.Sequence<byte> _925_authTag = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _926_valueOrError5;
STL.Result<Dafny.Sequence<byte>> _out96;
var _outcollector96 = (rd).ReadExact(_25_AlgorithmSuite_Compile.ID.TagLength(algorithmSuiteID));
_out96 = _outcollector96;
_926_valueOrError5 = _out96;
      if ((_926_valueOrError5).IsFailure()) {
        res = (_926_valueOrError5).PropagateFailure<_System.Tuple2<Dafny.Sequence<byte>,bool>>();
return res;
      }
      _925_authTag = (_926_valueOrError5).Extract();
      Dafny.Sequence<byte> _927_plaintext = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _928_valueOrError6;
STL.Result<Dafny.Sequence<byte>> _out97;
var _outcollector97 = _0_MessageBody_Compile.__default.Decrypt(_923_ciphertext, _925_authTag, algorithmSuiteID, _918_iv, key, _922_aad);
_out97 = _outcollector97;
_928_valueOrError6 = _out97;
      if ((_928_valueOrError6).IsFailure()) {
        res = (_928_valueOrError6).PropagateFailure<_System.Tuple2<Dafny.Sequence<byte>,bool>>();
return res;
      }
      _927_plaintext = (_928_valueOrError6).Extract();
      res = @STL.Result<_System.Tuple2<Dafny.Sequence<byte>,bool>>.create_Success(@_System.Tuple2<Dafny.Sequence<byte>,bool>.create(_927_plaintext, _914_final));
return res;
      return res;
    }
    public static Dafny.Sequence<byte> BodyAAD(Dafny.Sequence<byte> messageID, bool final, uint sequenceNumber, ulong length)
    {
    TAIL_CALL_START: ;
Dafny.Sequence<byte> aad = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _929_contentAAD;
      _929_contentAAD = (final) ? (_0_MessageBody_Compile.__default.BODY__AAD__CONTENT__FINAL__FRAME) : (_0_MessageBody_Compile.__default.BODY__AAD__CONTENT__REGULAR__FRAME);
      aad = (((messageID).Concat((_929_contentAAD))).Concat((STLUInt.__default.UInt32ToSeq(sequenceNumber)))).Concat((STLUInt.__default.UInt64ToSeq(length)));
      return aad;
    }
    public static STL.Result<Dafny.Sequence<byte>> Decrypt(Dafny.Sequence<byte> ciphertext, Dafny.Sequence<byte> authTag, ushort algorithmSuiteID, Dafny.Sequence<byte> iv, Dafny.Sequence<byte> key, Dafny.Sequence<byte> aad)
    {
    TAIL_CALL_START: ;
STL.Result<Dafny.Sequence<byte>> res = STL.Result<Dafny.Sequence<byte>>.Default;
      EncryptionSuites.EncryptionSuite _930_encAlg;
      _930_encAlg = _25_AlgorithmSuite_Compile.ID.EncryptionSuite(algorithmSuiteID);
      STL.Result<Dafny.Sequence<byte>> _out98;
var _outcollector98 = AESEncryption.AES_GCM.AESDecrypt(_930_encAlg, key, ciphertext, authTag, iv, aad);
_out98 = _outcollector98;
res = _out98;
      return res;
    }
    public static uint START__SEQUENCE__NUMBER { get {
      return 1U;
    } }
    public static uint ENDFRAME__SEQUENCE__NUMBER { get {
      return 4294967295U;
    } }
    public static Dafny.Sequence<byte> BODY__AAD__CONTENT__FINAL__FRAME { get {
      return (UTF8.__default.Encode(Dafny.Sequence<char>.FromString("AWSKMSEncryptionClient Final Frame"))).dtor_value;
    } }
    public static Dafny.Sequence<byte> BODY__AAD__CONTENT__REGULAR__FRAME { get {
      return (UTF8.__default.Encode(Dafny.Sequence<char>.FromString("AWSKMSEncryptionClient Frame"))).dtor_value;
    } }
  }
} // end of namespace _0_MessageBody_Compile
namespace Arrays {


} // end of namespace Arrays
namespace BouncyCastleCryptoMac {




  public class CipherParameters {
    public readonly byte[] key;
public CipherParameters(byte[] key) {
      this.key = key;
    }
    public override bool Equals(object other) {
      var oth = other as BouncyCastleCryptoMac.CipherParameters;
return oth != null && this.key == oth.key;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.key));
return (int) hash;
    }
    public override string ToString() {
      string s = "BouncyCastleCryptoMac_Compile.CipherParameters.KeyParameter";
s += "(";
s += Dafny.Helpers.ToString(this.key);
s += ")";
return s;
    }
    static CipherParameters theDefault;
public static CipherParameters Default {
      get {
        if (theDefault == null) {
          theDefault = new BouncyCastleCryptoMac.CipherParameters(new byte[0]);
        }
        return theDefault;
      }
    }
    public static CipherParameters _DafnyDefaultValue() { return Default; }
public static CipherParameters create(byte[] key) {
      return new CipherParameters(key);
    }
    public bool is_KeyParameter { get { return true; } }
public byte[] dtor_key {
      get {
        return this.key;
      }
    }
  }

  public interface Mac {
    Dafny.Sequence<char> getAlgorithmName();
BigInteger getMacSize();
void init(BouncyCastleCryptoMac.CipherParameters @params);
void reset();
void updateSingle(byte input);
void update(byte[] input, BigInteger inOff, BigInteger len);
BigInteger doFinal(byte[] output, BigInteger outOff);
  }
  public class _Companion_Mac {
  }

  public partial class HMac : BouncyCastleCryptoMac.Mac {
    public Digests.HMAC_ALGORITHM _algorithm = Digests.HMAC_ALGORITHM.Default;
public Digests.HMAC_ALGORITHM algorithm { get {
      return this._algorithm;
    } }
    public void updateAll(byte[] input)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).update(input, BigInteger.Zero, new BigInteger((input).Length));
    }
  }

} // end of namespace BouncyCastleCryptoMac
namespace _167_HKDFSpec_Compile {




} // end of namespace _167_HKDFSpec_Compile
namespace _171_HKDF_Compile {







  public partial class __default {
    public static byte[] extract(Digests.HMAC_ALGORITHM which__sha, BouncyCastleCryptoMac.HMac hmac, byte[] salt, byte[] ikm)
    {
    TAIL_CALL_START: ;
byte[] prk = new byte[0];
      BouncyCastleCryptoMac.CipherParameters _931_params;
      _931_params = @BouncyCastleCryptoMac.CipherParameters.create(salt);
      (hmac).init(_931_params);
      { }
      (hmac).updateAll(ikm);
      var _nw6 = new byte[(int)((hmac).getMacSize())];
      prk = _nw6;
      BigInteger _932___v0;
BigInteger _out99;
var _outcollector99 = (hmac).doFinal(prk, BigInteger.Zero);
_out99 = _outcollector99;
_932___v0 = _out99;
      prk = prk;
return prk;
      return prk;
    }
    public static byte[] expand(Digests.HMAC_ALGORITHM which__sha, BouncyCastleCryptoMac.HMac hmac, byte[] prk, byte[] info, BigInteger n)
    {
      byte[] a = new byte[0];
      BouncyCastleCryptoMac.CipherParameters _933_params;
      _933_params = @BouncyCastleCryptoMac.CipherParameters.create(prk);
      (hmac).init(_933_params);
      { }
      { }
      var _nw7 = new byte[(int)((n) * ((hmac).getMacSize()))];
      a = _nw7;
      byte[] _934_TiArr;
      var _nw8 = new byte[(int)((hmac).getMacSize())];
      _934_TiArr = _nw8;
      (hmac).updateAll(info);
      (hmac).updateSingle((byte)(1));
      BigInteger _935___v1;
BigInteger _out100;
var _outcollector100 = (hmac).doFinal(_934_TiArr, BigInteger.Zero);
_out100 = _outcollector100;
_935___v1 = _out100;
      Arrays.Array.copyTo<byte>(_934_TiArr, a, BigInteger.Zero);
      { }
      BigInteger _936_i;
      _936_i = BigInteger.One;
      { }
      while ((_936_i) < (n)) {
        (hmac).updateAll(_934_TiArr);
        (hmac).updateAll(info);
        (hmac).updateSingle((byte)((_936_i) + (BigInteger.One)));
        { }
        { }
        BigInteger _937___v2;
BigInteger _out101;
var _outcollector101 = (hmac).doFinal(_934_TiArr, BigInteger.Zero);
_out101 = _outcollector101;
_937___v2 = _out101;
        Arrays.Array.copyTo<byte>(_934_TiArr, a, (_936_i) * ((hmac).getMacSize()));
        { }
        _936_i = (_936_i) + (BigInteger.One);
      }
      return a;
    }
    public static byte[] hkdf(Digests.HMAC_ALGORITHM which__sha, STL.Option<byte[]> salt, byte[] ikm, byte[] info, BigInteger L)
    {
    TAIL_CALL_START: ;
byte[] okm = new byte[0];
      if ((L).Sign == 0) {
        var _nw9 = new byte[(int)(BigInteger.Zero)];
        okm = _nw9;
return okm;
      }
      BouncyCastleCryptoMac.HMac _938_hmac;
      var _nw10 = new BouncyCastleCryptoMac.HMac(which__sha);
      _938_hmac = _nw10;
      byte[] _939_saltNonEmpty = new byte[0];
      STL.Option<byte[]> _source13 = salt;
if (_source13.is_None) {
        var _nw11 = new byte[(int)((_938_hmac).getMacSize())];
var _arrayinit2 = Dafny.Helpers.Id<Func<Func<BigInteger,byte>>>(() => ((System.Func<BigInteger, byte>)((_940___v3) => {
          return 0;
        })))();
for (var _arrayinit_02 = 0; _arrayinit_02 < _nw11.Length; _arrayinit_02++) {
          _nw11[(int)(_arrayinit_02)] = _arrayinit2(_arrayinit_02);
        }
        _939_saltNonEmpty = _nw11;
      } else {
        byte[] _941_s = ((STL.Option_Some<byte[]>)_source13).@get;
        _939_saltNonEmpty = _941_s;
      }
      { }
      BigInteger _942_n;
      _942_n = (BigInteger.One) + (Dafny.Helpers.EuclideanDivision((L) - (BigInteger.One), (_938_hmac).getMacSize()));
      { }
      byte[] _943_prk;
byte[] _out102;
var _outcollector102 = _171_HKDF_Compile.__default.extract(which__sha, _938_hmac, _939_saltNonEmpty, ikm);
_out102 = _outcollector102;
_943_prk = _out102;
      byte[] _out103;
var _outcollector103 = _171_HKDF_Compile.__default.expand(which__sha, _938_hmac, _943_prk, info, _942_n);
_out103 = _outcollector103;
okm = _out103;
      if ((new BigInteger((okm).Length)) > (L)) {
        byte[] _out104;
var _outcollector104 = Arrays.Array.copy<byte>(okm, L);
_out104 = _outcollector104;
okm = _out104;
      }
      { }
      return okm;
    }
  }
} // end of namespace _171_HKDF_Compile
namespace _176_ESDKClient_Compile {
















  public partial class __default {
    public static STL.Result<Dafny.Sequence<byte>> Encrypt(Dafny.Sequence<byte> plaintext, _111_CMMDefs_Compile.CMM cmm, Dafny.Sequence<_System.Tuple2<Dafny.Sequence<byte>,Dafny.Sequence<byte>>> encryptionContext)
    {
      STL.Result<Dafny.Sequence<byte>> res = STL.Result<Dafny.Sequence<byte>>.Default;
      Materials.EncryptionMaterials _944_encMat = Materials.ValidEncryptionMaterials.Witness;
      STL.Result<Materials.EncryptionMaterials> _945_valueOrError0;
STL.Result<Materials.EncryptionMaterials> _out105;
var _outcollector105 = (cmm).GetEncryptionMaterials(encryptionContext, @STL.Option<ushort>.create_None(), @STL.Option<BigInteger>.create_Some(new BigInteger((plaintext).Count)));
_out105 = _outcollector105;
_945_valueOrError0 = _out105;
      if ((_945_valueOrError0).IsFailure()) {
        res = (_945_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _944_encMat = (_945_valueOrError0).Extract();
      Materials.DataKeyMaterials _946_dataKeyMaterials;
      _946_dataKeyMaterials = (_944_encMat).dtor_dataKeyMaterials;
      if ((STLUInt.__default.UINT16__LIMIT) <= (new BigInteger(((_946_dataKeyMaterials).dtor_encryptedDataKeys).Count))) {
        res = @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("Number of EDKs exceeds the allowed maximum."));
return res;
      }
      Dafny.Sequence<byte> _947_messageID;
Dafny.Sequence<byte> _out106;
var _outcollector106 = Random.__default.GenerateBytes((int)(_76_MessageHeader_Compile.__default.MESSAGE__ID__LEN));
_out106 = _outcollector106;
_947_messageID = _out106;
      Dafny.Sequence<byte> _948_derivedDataKey;
Dafny.Sequence<byte> _out107;
var _outcollector107 = _176_ESDKClient_Compile.__default.DeriveKey((_946_dataKeyMaterials).dtor_plaintextDataKey, (_946_dataKeyMaterials).dtor_algorithmSuiteID, _947_messageID);
_out107 = _outcollector107;
_948_derivedDataKey = _out107;
      uint _949_frameLength;
      _949_frameLength = 4096U;
      _76_MessageHeader_Compile.HeaderBody _950_headerBody;
      _950_headerBody = @_76_MessageHeader_Compile.HeaderBody.create(_76_MessageHeader_Compile.__default.VERSION__1, _76_MessageHeader_Compile.__default.TYPE__CUSTOMER__AED, (_946_dataKeyMaterials).dtor_algorithmSuiteID, _947_messageID, (_944_encMat).dtor_encryptionContext, @_76_MessageHeader_Compile.EncryptedDataKeys.create((_946_dataKeyMaterials).dtor_encryptedDataKeys), @_76_MessageHeader_Compile.ContentType.create_Framed(), (byte)(_25_AlgorithmSuite_Compile.ID.IVLength((_946_dataKeyMaterials).dtor_algorithmSuiteID)), _949_frameLength);
      _54_Streams_Compile.StringWriter _951_wr;
      var _nw12 = new _54_Streams_Compile.StringWriter();
_nw12.__ctor();
      _951_wr = _nw12;
      BigInteger _952___v0 = BigInteger.Zero;
      STL.Result<BigInteger> _953_valueOrError1;
STL.Result<BigInteger> _out108;
var _outcollector108 = _83_Serialize_Compile.__default.SerializeHeaderBody(_951_wr, _950_headerBody);
_out108 = _outcollector108;
_953_valueOrError1 = _out108;
      if ((_953_valueOrError1).IsFailure()) {
        res = (_953_valueOrError1).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _952___v0 = (_953_valueOrError1).Extract();
      Dafny.Sequence<byte> _954_unauthenticatedHeader;
      _954_unauthenticatedHeader = _951_wr.data;
      Dafny.Sequence<byte> _955_iv;
      _955_iv = ((System.Func<Dafny.Sequence<byte>>) (() => {
        BigInteger dim10 = _25_AlgorithmSuite_Compile.ID.IVLength((_946_dataKeyMaterials).dtor_algorithmSuiteID);
var arr10 = new byte[(int)(dim10)];
for (int i10 = 0; i10 < dim10; i10++) { 
          var _956___v1 = (BigInteger) i10;
arr10[(int)(_956___v1)] = 0;
        }
        return Dafny.Sequence<byte>.FromArray(arr10);
      }))();
      AESEncryption.EncryptionOutput _957_encryptionOutput = AESEncryption.EncryptionOutput.Default;
      STL.Result<AESEncryption.EncryptionOutput> _958_valueOrError2;
STL.Result<AESEncryption.EncryptionOutput> _out109;
var _outcollector109 = AESEncryption.AES_GCM.AESEncrypt(_25_AlgorithmSuite_Compile.ID.EncryptionSuite((_946_dataKeyMaterials).dtor_algorithmSuiteID), _955_iv, _948_derivedDataKey, Dafny.Sequence<byte>.FromElements(), _954_unauthenticatedHeader);
_out109 = _outcollector109;
_958_valueOrError2 = _out109;
      if ((_958_valueOrError2).IsFailure()) {
        res = (_958_valueOrError2).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _957_encryptionOutput = (_958_valueOrError2).Extract();
      _76_MessageHeader_Compile.HeaderAuthentication _959_headerAuthentication;
      _959_headerAuthentication = @_76_MessageHeader_Compile.HeaderAuthentication.create(_955_iv, (_957_encryptionOutput).dtor_authTag);
      BigInteger _960___v2 = BigInteger.Zero;
      STL.Result<BigInteger> _961_valueOrError3;
STL.Result<BigInteger> _out110;
var _outcollector110 = _83_Serialize_Compile.__default.SerializeHeaderAuthentication(_951_wr, _959_headerAuthentication);
_out110 = _outcollector110;
_961_valueOrError3 = _out110;
      if ((_961_valueOrError3).IsFailure()) {
        res = (_961_valueOrError3).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _960___v2 = (_961_valueOrError3).Extract();
      Dafny.Sequence<byte> _962_body = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _963_valueOrError4;
STL.Result<Dafny.Sequence<byte>> _out111;
var _outcollector111 = _0_MessageBody_Compile.__default.EncryptMessageBody(plaintext, new BigInteger(_949_frameLength), _947_messageID, _948_derivedDataKey, (_946_dataKeyMaterials).dtor_algorithmSuiteID);
_out111 = _outcollector111;
_963_valueOrError4 = _out111;
      if ((_963_valueOrError4).IsFailure()) {
        res = (_963_valueOrError4).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _962_body = (_963_valueOrError4).Extract();
      Dafny.Sequence<byte> _964_msg;
      _964_msg = (_951_wr.data).Concat((_962_body));
      STL.Option<Signature.ECDSAParams> _source14 = _25_AlgorithmSuite_Compile.ID.SignatureType((_946_dataKeyMaterials).dtor_algorithmSuiteID);
if (_source14.is_None) {
      } else {
        Signature.ECDSAParams _965_ecdsaParams = ((STL.Option_Some<Signature.ECDSAParams>)_source14).@get;
        Dafny.Sequence<byte> _966_digest;
Dafny.Sequence<byte> _out112;
var _outcollector112 = Signature.ECDSA.Digest(_965_ecdsaParams, _964_msg);
_out112 = _outcollector112;
_966_digest = _out112;
        STL.Option<Dafny.Sequence<byte>> _967_signResult;
STL.Option<Dafny.Sequence<byte>> _out113;
var _outcollector113 = Signature.ECDSA.Sign(_965_ecdsaParams, ((_944_encMat).dtor_signingKey).dtor_get, _966_digest);
_out113 = _outcollector113;
_967_signResult = _out113;
        STL.Option<Dafny.Sequence<byte>> _source15 = _967_signResult;
if (_source15.is_None) {
          res = @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("Message signing failed"));
return res;
        } else {
          Dafny.Sequence<byte> _968_bytes = ((STL.Option_Some<Dafny.Sequence<byte>>)_source15).@get;
          _964_msg = ((_964_msg).Concat((STLUInt.__default.UInt16ToSeq((ushort)(_968_bytes).Count)))).Concat((_968_bytes));
        }
      }
      res = @STL.Result<Dafny.Sequence<byte>>.create_Success(_964_msg);
return res;
      return res;
    }
    public static Dafny.Sequence<byte> DeriveKey(Dafny.Sequence<byte> plaintextDataKey, ushort algorithmSuiteID, Dafny.Sequence<byte> messageID)
    {
    TAIL_CALL_START: ;
Dafny.Sequence<byte> derivedDataKey = Dafny.Sequence<byte>.Empty;
      Digests.HMAC_ALGORITHM _969_whichSHA;
      _969_whichSHA = ((_25_AlgorithmSuite_Compile.__default.Suite).Select(algorithmSuiteID)).dtor_hkdf;
      if ((_969_whichSHA).Equals((@Digests.HMAC_ALGORITHM.create_HmacNOSHA()))) {
        derivedDataKey = plaintextDataKey;
return derivedDataKey;
      }
      byte[] _970_inputKeyMaterials;
byte[] _out114;
var _outcollector114 = STL.__default.SeqToArray<byte>(plaintextDataKey);
_out114 = _outcollector114;
_970_inputKeyMaterials = _out114;
      Dafny.Sequence<byte> _971_infoSeq;
      _971_infoSeq = (STLUInt.__default.UInt16ToSeq((ushort)(algorithmSuiteID))).Concat((messageID));
      byte[] _972_info;
byte[] _out115;
var _outcollector115 = STL.__default.SeqToArray<byte>(_971_infoSeq);
_out115 = _outcollector115;
_972_info = _out115;
      BigInteger _973_len;
      _973_len = _25_AlgorithmSuite_Compile.ID.KeyLength(algorithmSuiteID);
      byte[] _974_derivedKey;
byte[] _out116;
var _outcollector116 = _171_HKDF_Compile.__default.hkdf(_969_whichSHA, @STL.Option<byte[]>.create_None(), _970_inputKeyMaterials, _972_info, _973_len);
_out116 = _outcollector116;
_974_derivedKey = _out116;
      derivedDataKey = Dafny.Helpers.SeqFromArray(_974_derivedKey);
return derivedDataKey;
      return derivedDataKey;
    }
    public static STL.Result<Dafny.Sequence<byte>> Decrypt(Dafny.Sequence<byte> message, _111_CMMDefs_Compile.CMM cmm)
    {
      STL.Result<Dafny.Sequence<byte>> res = STL.Result<Dafny.Sequence<byte>>.Default;
      _54_Streams_Compile.StringReader _975_rd;
      var _nw13 = new _54_Streams_Compile.StringReader();
_nw13.FromSeq(message);
      _975_rd = _nw13;
      _76_MessageHeader_Compile.Header _976_header = _76_MessageHeader_Compile.Header.Default;
      STL.Result<_76_MessageHeader_Compile.Header> _977_valueOrError0;
STL.Result<_76_MessageHeader_Compile.Header> _out117;
var _outcollector117 = _0_Deserialize_Compile.__default.DeserializeHeader(_975_rd);
_out117 = _outcollector117;
_977_valueOrError0 = _out117;
      if ((_977_valueOrError0).IsFailure()) {
        res = (_977_valueOrError0).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _976_header = (_977_valueOrError0).Extract();
      Materials.DecryptionMaterials _978_decMat = Materials.ValidDecryptionMaterials.Witness;
      STL.Result<Materials.DecryptionMaterials> _979_valueOrError1;
STL.Result<Materials.DecryptionMaterials> _out118;
var _outcollector118 = (cmm).DecryptMaterials(((_976_header).dtor_body).dtor_algorithmSuiteID, (((_976_header).dtor_body).dtor_encryptedDataKeys).dtor_entries, ((_976_header).dtor_body).dtor_aad);
_out118 = _outcollector118;
_979_valueOrError1 = _out118;
      if ((_979_valueOrError1).IsFailure()) {
        res = (_979_valueOrError1).PropagateFailure<Dafny.Sequence<byte>>();
return res;
      }
      _978_decMat = (_979_valueOrError1).Extract();
      Dafny.Sequence<byte> _980_decryptionKey;
Dafny.Sequence<byte> _out119;
var _outcollector119 = _176_ESDKClient_Compile.__default.DeriveKey((_978_decMat).dtor_plaintextDataKey, (_978_decMat).dtor_algorithmSuiteID, ((_976_header).dtor_body).dtor_messageID);
_out119 = _outcollector119;
_980_decryptionKey = _out119;
      Dafny.Sequence<byte> _981_plaintext = Dafny.Sequence<byte>.Empty;
      _76_MessageHeader_Compile.ContentType _source16 = ((_976_header).dtor_body).dtor_contentType;
if (_source16.is_NonFramed) {
      } else {
        STL.Result<Dafny.Sequence<byte>> _982_valueOrError2;
STL.Result<Dafny.Sequence<byte>> _out120;
var _outcollector120 = _0_MessageBody_Compile.__default.DecryptFramedMessageBody(_975_rd, (_978_decMat).dtor_algorithmSuiteID, _980_decryptionKey, new BigInteger(((_976_header).dtor_body).dtor_frameLength), ((_976_header).dtor_body).dtor_messageID);
_out120 = _outcollector120;
_982_valueOrError2 = _out120;
        if ((_982_valueOrError2).IsFailure()) {
          res = (_982_valueOrError2).PropagateFailure<Dafny.Sequence<byte>>();
return res;
        }
        _981_plaintext = (_982_valueOrError2).Extract();
      }
      STL.Option<Signature.ECDSAParams> _source17 = _25_AlgorithmSuite_Compile.ID.SignatureType((_978_decMat).dtor_algorithmSuiteID);
if (_source17.is_None) {
      } else {
        Signature.ECDSAParams _983_ecdsaParams = ((STL.Option_Some<Signature.ECDSAParams>)_source17).@get;
        Dafny.Sequence<byte> _984_msg;
        _984_msg = (message).Take(_975_rd.pos);
        ushort _985_signatureLength = 0;
        STL.Result<ushort> _986_valueOrError3;
STL.Result<ushort> _out121;
var _outcollector121 = (_975_rd).ReadUInt16();
_out121 = _outcollector121;
_986_valueOrError3 = _out121;
        if ((_986_valueOrError3).IsFailure()) {
          res = (_986_valueOrError3).PropagateFailure<Dafny.Sequence<byte>>();
return res;
        }
        _985_signatureLength = (_986_valueOrError3).Extract();
        Dafny.Sequence<byte> _987_sig = Dafny.Sequence<byte>.Empty;
        STL.Result<Dafny.Sequence<byte>> _988_valueOrError4;
STL.Result<Dafny.Sequence<byte>> _out122;
var _outcollector122 = (_975_rd).ReadExact(new BigInteger(_985_signatureLength));
_out122 = _outcollector122;
_988_valueOrError4 = _out122;
        if ((_988_valueOrError4).IsFailure()) {
          res = (_988_valueOrError4).PropagateFailure<Dafny.Sequence<byte>>();
return res;
        }
        _987_sig = (_988_valueOrError4).Extract();
        Dafny.Sequence<byte> _989_digest;
Dafny.Sequence<byte> _out123;
var _outcollector123 = Signature.ECDSA.Digest(_983_ecdsaParams, _984_msg);
_out123 = _outcollector123;
_989_digest = _out123;
        bool _990_signatureVerified;
        _990_signatureVerified = Signature.ECDSA.Verify(_983_ecdsaParams, ((_978_decMat).dtor_verificationKey).dtor_get, _989_digest, _987_sig);
        if (!(_990_signatureVerified)) {
          res = @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("signature not verified"));
return res;
        }
      }
      if (((_975_rd).Available()).Sign != 0) {
        res = @STL.Result<Dafny.Sequence<byte>>.create_Failure(Dafny.Sequence<char>.FromString("message contains additional bytes at end"));
return res;
      }
      res = @STL.Result<Dafny.Sequence<byte>>.create_Success(_981_plaintext);
return res;
      return res;
    }
  }
} // end of namespace _176_ESDKClient_Compile
namespace TestVectorExterns {













  public class MasterKey {
    public readonly Dafny.Sequence<char> masterKeyType;
public readonly TestVectorExterns.Key key;
public readonly STL.Option<Dafny.Sequence<char>> providerID;
public readonly STL.Option<Dafny.Sequence<char>> encryptionAlgorithm;
public readonly STL.Option<Dafny.Sequence<char>> paddingAlgorithm;
public readonly STL.Option<Dafny.Sequence<char>> paddingHash;
public MasterKey(Dafny.Sequence<char> masterKeyType, TestVectorExterns.Key key, STL.Option<Dafny.Sequence<char>> providerID, STL.Option<Dafny.Sequence<char>> encryptionAlgorithm, STL.Option<Dafny.Sequence<char>> paddingAlgorithm, STL.Option<Dafny.Sequence<char>> paddingHash) {
      this.masterKeyType = masterKeyType;
this.key = key;
this.providerID = providerID;
this.encryptionAlgorithm = encryptionAlgorithm;
this.paddingAlgorithm = paddingAlgorithm;
this.paddingHash = paddingHash;
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorExterns.MasterKey;
return oth != null && object.Equals(this.masterKeyType, oth.masterKeyType) && object.Equals(this.key, oth.key) && object.Equals(this.providerID, oth.providerID) && object.Equals(this.encryptionAlgorithm, oth.encryptionAlgorithm) && object.Equals(this.paddingAlgorithm, oth.paddingAlgorithm) && object.Equals(this.paddingHash, oth.paddingHash);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.masterKeyType));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.key));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.providerID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encryptionAlgorithm));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.paddingAlgorithm));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.paddingHash));
return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorExterns_Compile.MasterKey.MasterKey";
s += "(";
s += Dafny.Helpers.ToString(this.masterKeyType);
s += ", ";
s += Dafny.Helpers.ToString(this.key);
s += ", ";
s += Dafny.Helpers.ToString(this.providerID);
s += ", ";
s += Dafny.Helpers.ToString(this.encryptionAlgorithm);
s += ", ";
s += Dafny.Helpers.ToString(this.paddingAlgorithm);
s += ", ";
s += Dafny.Helpers.ToString(this.paddingHash);
s += ")";
return s;
    }
    static MasterKey theDefault;
public static MasterKey Default {
      get {
        if (theDefault == null) {
          theDefault = new TestVectorExterns.MasterKey(Dafny.Sequence<char>.Empty, TestVectorExterns.Key.Default, STL.Option<Dafny.Sequence<char>>.Default, STL.Option<Dafny.Sequence<char>>.Default, STL.Option<Dafny.Sequence<char>>.Default, STL.Option<Dafny.Sequence<char>>.Default);
        }
        return theDefault;
      }
    }
    public static MasterKey _DafnyDefaultValue() { return Default; }
public static MasterKey create(Dafny.Sequence<char> masterKeyType, TestVectorExterns.Key key, STL.Option<Dafny.Sequence<char>> providerID, STL.Option<Dafny.Sequence<char>> encryptionAlgorithm, STL.Option<Dafny.Sequence<char>> paddingAlgorithm, STL.Option<Dafny.Sequence<char>> paddingHash) {
      return new MasterKey(masterKeyType, key, providerID, encryptionAlgorithm, paddingAlgorithm, paddingHash);
    }
    public bool is_MasterKey { get { return true; } }
public Dafny.Sequence<char> dtor_masterKeyType {
      get {
        return this.masterKeyType;
      }
    }
    public TestVectorExterns.Key dtor_key {
      get {
        return this.key;
      }
    }
    public STL.Option<Dafny.Sequence<char>> dtor_providerID {
      get {
        return this.providerID;
      }
    }
    public STL.Option<Dafny.Sequence<char>> dtor_encryptionAlgorithm {
      get {
        return this.encryptionAlgorithm;
      }
    }
    public STL.Option<Dafny.Sequence<char>> dtor_paddingAlgorithm {
      get {
        return this.paddingAlgorithm;
      }
    }
    public STL.Option<Dafny.Sequence<char>> dtor_paddingHash {
      get {
        return this.paddingHash;
      }
    }
  }

  public class Key {
    public readonly bool encrypt;
public readonly bool decrypt;
public readonly Dafny.Sequence<char> keyType;
public readonly Dafny.Sequence<char> keyID;
public readonly STL.Option<Dafny.Sequence<char>> algorithm;
public readonly STL.Option<ushort> bits;
public readonly STL.Option<Dafny.Sequence<char>> encoding;
public readonly STL.Option<Dafny.Sequence<char>> material;
public readonly Dafny.Sequence<char> keyIndex;
public Key(bool encrypt, bool decrypt, Dafny.Sequence<char> keyType, Dafny.Sequence<char> keyID, STL.Option<Dafny.Sequence<char>> algorithm, STL.Option<ushort> bits, STL.Option<Dafny.Sequence<char>> encoding, STL.Option<Dafny.Sequence<char>> material, Dafny.Sequence<char> keyIndex) {
      this.encrypt = encrypt;
this.decrypt = decrypt;
this.keyType = keyType;
this.keyID = keyID;
this.algorithm = algorithm;
this.bits = bits;
this.encoding = encoding;
this.material = material;
this.keyIndex = keyIndex;
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorExterns.Key;
return oth != null && this.encrypt == oth.encrypt && this.decrypt == oth.decrypt && object.Equals(this.keyType, oth.keyType) && object.Equals(this.keyID, oth.keyID) && object.Equals(this.algorithm, oth.algorithm) && object.Equals(this.bits, oth.bits) && object.Equals(this.encoding, oth.encoding) && object.Equals(this.material, oth.material) && object.Equals(this.keyIndex, oth.keyIndex);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encrypt));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.decrypt));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyType));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.algorithm));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.bits));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.encoding));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.material));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.keyIndex));
return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorExterns_Compile.Key.Key";
s += "(";
s += Dafny.Helpers.ToString(this.encrypt);
s += ", ";
s += Dafny.Helpers.ToString(this.decrypt);
s += ", ";
s += Dafny.Helpers.ToString(this.keyType);
s += ", ";
s += Dafny.Helpers.ToString(this.keyID);
s += ", ";
s += Dafny.Helpers.ToString(this.algorithm);
s += ", ";
s += Dafny.Helpers.ToString(this.bits);
s += ", ";
s += Dafny.Helpers.ToString(this.encoding);
s += ", ";
s += Dafny.Helpers.ToString(this.material);
s += ", ";
s += Dafny.Helpers.ToString(this.keyIndex);
s += ")";
return s;
    }
    static Key theDefault;
public static Key Default {
      get {
        if (theDefault == null) {
          theDefault = new TestVectorExterns.Key(false, false, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, STL.Option<Dafny.Sequence<char>>.Default, STL.Option<ushort>.Default, STL.Option<Dafny.Sequence<char>>.Default, STL.Option<Dafny.Sequence<char>>.Default, Dafny.Sequence<char>.Empty);
        }
        return theDefault;
      }
    }
    public static Key _DafnyDefaultValue() { return Default; }
public static Key create(bool encrypt, bool decrypt, Dafny.Sequence<char> keyType, Dafny.Sequence<char> keyID, STL.Option<Dafny.Sequence<char>> algorithm, STL.Option<ushort> bits, STL.Option<Dafny.Sequence<char>> encoding, STL.Option<Dafny.Sequence<char>> material, Dafny.Sequence<char> keyIndex) {
      return new Key(encrypt, decrypt, keyType, keyID, algorithm, bits, encoding, material, keyIndex);
    }
    public bool is_Key { get { return true; } }
public bool dtor_encrypt {
      get {
        return this.encrypt;
      }
    }
    public bool dtor_decrypt {
      get {
        return this.decrypt;
      }
    }
    public Dafny.Sequence<char> dtor_keyType {
      get {
        return this.keyType;
      }
    }
    public Dafny.Sequence<char> dtor_keyID {
      get {
        return this.keyID;
      }
    }
    public STL.Option<Dafny.Sequence<char>> dtor_algorithm {
      get {
        return this.algorithm;
      }
    }
    public STL.Option<ushort> dtor_bits {
      get {
        return this.bits;
      }
    }
    public STL.Option<Dafny.Sequence<char>> dtor_encoding {
      get {
        return this.encoding;
      }
    }
    public STL.Option<Dafny.Sequence<char>> dtor_material {
      get {
        return this.material;
      }
    }
    public Dafny.Sequence<char> dtor_keyIndex {
      get {
        return this.keyIndex;
      }
    }
  }

  public class TestCase {
    public readonly Dafny.Sequence<char> testID;
public readonly Dafny.Sequence<char> plaintext;
public readonly Dafny.Sequence<char> ciphertext;
public readonly Dafny.Sequence<TestVectorExterns.MasterKey> masterKeys;
public TestCase(Dafny.Sequence<char> testID, Dafny.Sequence<char> plaintext, Dafny.Sequence<char> ciphertext, Dafny.Sequence<TestVectorExterns.MasterKey> masterKeys) {
      this.testID = testID;
this.plaintext = plaintext;
this.ciphertext = ciphertext;
this.masterKeys = masterKeys;
    }
    public override bool Equals(object other) {
      var oth = other as TestVectorExterns.TestCase;
return oth != null && object.Equals(this.testID, oth.testID) && object.Equals(this.plaintext, oth.plaintext) && object.Equals(this.ciphertext, oth.ciphertext) && object.Equals(this.masterKeys, oth.masterKeys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
hash = ((hash << 5) + hash) + 0;
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.testID));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.plaintext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.ciphertext));
hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.masterKeys));
return (int) hash;
    }
    public override string ToString() {
      string s = "TestVectorExterns_Compile.TestCase.TestCase";
s += "(";
s += Dafny.Helpers.ToString(this.testID);
s += ", ";
s += Dafny.Helpers.ToString(this.plaintext);
s += ", ";
s += Dafny.Helpers.ToString(this.ciphertext);
s += ", ";
s += Dafny.Helpers.ToString(this.masterKeys);
s += ")";
return s;
    }
    static TestCase theDefault;
public static TestCase Default {
      get {
        if (theDefault == null) {
          theDefault = new TestVectorExterns.TestCase(Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<char>.Empty, Dafny.Sequence<TestVectorExterns.MasterKey>.Empty);
        }
        return theDefault;
      }
    }
    public static TestCase _DafnyDefaultValue() { return Default; }
public static TestCase create(Dafny.Sequence<char> testID, Dafny.Sequence<char> plaintext, Dafny.Sequence<char> ciphertext, Dafny.Sequence<TestVectorExterns.MasterKey> masterKeys) {
      return new TestCase(testID, plaintext, ciphertext, masterKeys);
    }
    public bool is_TestCase { get { return true; } }
public Dafny.Sequence<char> dtor_testID {
      get {
        return this.testID;
      }
    }
    public Dafny.Sequence<char> dtor_plaintext {
      get {
        return this.plaintext;
      }
    }
    public Dafny.Sequence<char> dtor_ciphertext {
      get {
        return this.ciphertext;
      }
    }
    public Dafny.Sequence<TestVectorExterns.MasterKey> dtor_masterKeys {
      get {
        return this.masterKeys;
      }
    }
  }

  public partial class __default {
    public static Dafny.Sequence<char> TestURIToPath(Dafny.Sequence<char> uri) {
      return (uri).Drop(new BigInteger(7));
    }
    public static STL.Result<Dafny.Sequence<TestVectorExterns.TestCase>> LoadManifest(Dafny.Sequence<char> path, Dafny.Map<Dafny.Sequence<char>,TestVectorExterns.Key> keys)
    {
      STL.Result<Dafny.Sequence<TestVectorExterns.TestCase>> testCases = STL.Result<Dafny.Sequence<TestVectorExterns.TestCase>>.Default;
      Dafny.Sequence<byte> _991_manifestBytes = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _992_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out124;
var _outcollector124 = TestVectorExterns.__default.ReadFile(path);
_out124 = _outcollector124;
_992_valueOrError0 = _out124;
      if ((_992_valueOrError0).IsFailure()) {
        testCases = (_992_valueOrError0).PropagateFailure<Dafny.Sequence<TestVectorExterns.TestCase>>();
return testCases;
      }
      _991_manifestBytes = (_992_valueOrError0).Extract();
      Dafny.Sequence<char> _993_manifestText = Dafny.Sequence<char>.Empty;
      STL.Result<Dafny.Sequence<char>> _994_valueOrError1;
      _994_valueOrError1 = UTF8.__default.Decode(_991_manifestBytes);
      if ((_994_valueOrError1).IsFailure()) {
        testCases = (_994_valueOrError1).PropagateFailure<Dafny.Sequence<TestVectorExterns.TestCase>>();
return testCases;
      }
      _993_manifestText = (_994_valueOrError1).Extract();
      STL.Result<Dafny.Sequence<TestVectorExterns.TestCase>> _995_res;
STL.Result<Dafny.Sequence<TestVectorExterns.TestCase>> _out125;
var _outcollector125 = TestVectorExterns.__default.ParseManifest(_993_manifestText, keys);
_out125 = _outcollector125;
_995_res = _out125;
      testCases = _995_res;
return testCases;
      return testCases;
    }
    public static STL.Result<Dafny.Sequence<TestVectorExterns.Key>> LoadKeys(Dafny.Sequence<char> path)
    {
      STL.Result<Dafny.Sequence<TestVectorExterns.Key>> keys = STL.Result<Dafny.Sequence<TestVectorExterns.Key>>.Default;
      Dafny.Sequence<byte> _996_keysBytes = Dafny.Sequence<byte>.Empty;
      STL.Result<Dafny.Sequence<byte>> _997_valueOrError0;
STL.Result<Dafny.Sequence<byte>> _out126;
var _outcollector126 = TestVectorExterns.__default.ReadFile(path);
_out126 = _outcollector126;
_997_valueOrError0 = _out126;
      if ((_997_valueOrError0).IsFailure()) {
        keys = (_997_valueOrError0).PropagateFailure<Dafny.Sequence<TestVectorExterns.Key>>();
return keys;
      }
      _996_keysBytes = (_997_valueOrError0).Extract();
      Dafny.Sequence<char> _998_keysText = Dafny.Sequence<char>.Empty;
      STL.Result<Dafny.Sequence<char>> _999_valueOrError1;
      _999_valueOrError1 = UTF8.__default.Decode(_996_keysBytes);
      if ((_999_valueOrError1).IsFailure()) {
        keys = (_999_valueOrError1).PropagateFailure<Dafny.Sequence<TestVectorExterns.Key>>();
return keys;
      }
      _998_keysText = (_999_valueOrError1).Extract();
      STL.Result<Dafny.Sequence<TestVectorExterns.Key>> _1000_res;
STL.Result<Dafny.Sequence<TestVectorExterns.Key>> _out127;
var _outcollector127 = TestVectorExterns.__default.ParseKeys(_998_keysText);
_out127 = _outcollector127;
_1000_res = _out127;
      keys = _1000_res;
return keys;
      return keys;
    }
    public static void Main()
    {
    TAIL_CALL_START: ;
      STL.Result<Dafny.Sequence<TestVectorExterns.Key>> _1001_keys;
STL.Result<Dafny.Sequence<TestVectorExterns.Key>> _out128;
var _outcollector128 = TestVectorExterns.__default.LoadKeys(Dafny.Sequence<char>.FromString("keys.json"));
_out128 = _outcollector128;
_1001_keys = _out128;
      if ((_1001_keys).is_Failure) {
        Dafny.Helpers.Print((_1001_keys).dtor_error);
        return;
      }
      Dafny.Map<Dafny.Sequence<char>,TestVectorExterns.Key> _1002_keyMap;
      _1002_keyMap = Dafny.Map<Dafny.Sequence<char>,TestVectorExterns.Key>.FromElements();
      BigInteger _1003_i;
      _1003_i = BigInteger.Zero;
      while ((_1003_i) < (new BigInteger(((_1001_keys).dtor_value).Count))) {
        _1002_keyMap = (_1002_keyMap).Update((((_1001_keys).dtor_value).Select(_1003_i)).dtor_keyIndex, ((_1001_keys).dtor_value).Select(_1003_i));
        _1003_i = (_1003_i) + (BigInteger.One);
      }
      STL.Result<Dafny.Sequence<TestVectorExterns.TestCase>> _1004_testVectors;
STL.Result<Dafny.Sequence<TestVectorExterns.TestCase>> _out129;
var _outcollector129 = TestVectorExterns.__default.LoadManifest(Dafny.Sequence<char>.FromString("manifest.json"), _1002_keyMap);
_out129 = _outcollector129;
_1004_testVectors = _out129;
      if ((_1004_testVectors).is_Failure) {
        Dafny.Helpers.Print((_1004_testVectors).dtor_error);
        return;
      }
      BigInteger _1005_j;
      _1005_j = BigInteger.Zero;
      BigInteger _1006_failCount;
      _1006_failCount = BigInteger.Zero;
      BigInteger _1007_passCount;
      _1007_passCount = BigInteger.Zero;
      BigInteger _1008_skipCount;
      _1008_skipCount = BigInteger.Zero;
      while ((_1005_j) < (new BigInteger(((_1004_testVectors).dtor_value).Count))) {
        TestVectorExterns.TestCase _1009_toTest;
        _1009_toTest = ((_1004_testVectors).dtor_value).Select(_1005_j);
        STL.Result<Dafny.Sequence<byte>> _1010_plaintext;
STL.Result<Dafny.Sequence<byte>> _out130;
var _outcollector130 = TestVectorExterns.__default.ReadFile(TestVectorExterns.__default.TestURIToPath((_1009_toTest).dtor_plaintext));
_out130 = _outcollector130;
_1010_plaintext = _out130;
        if ((_1010_plaintext).is_Failure) {
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Failure reading plaintext: "));
Dafny.Helpers.Print((_1010_plaintext).dtor_error);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
          return;
        }
        STL.Result<Dafny.Sequence<byte>> _1011_ciphertext;
STL.Result<Dafny.Sequence<byte>> _out131;
var _outcollector131 = TestVectorExterns.__default.ReadFile(TestVectorExterns.__default.TestURIToPath((_1009_toTest).dtor_ciphertext));
_out131 = _outcollector131;
_1011_ciphertext = _out131;
        if ((_1011_ciphertext).is_Failure) {
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Failure reading ciphertext: "));
Dafny.Helpers.Print((_1011_ciphertext).dtor_error);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
          return;
        }
        Dafny.Sequence<TestVectorExterns.MasterKey> _1012_keysToTest;
        _1012_keysToTest = (_1009_toTest).dtor_masterKeys;
        bool _1013_allKMS;
        _1013_allKMS = true;
        BigInteger _1014_allKMSIndex;
        _1014_allKMSIndex = BigInteger.Zero;
        while ((_1014_allKMSIndex) < (new BigInteger((_1012_keysToTest).Count))) {
          if (!(((_1012_keysToTest).Select(_1014_allKMSIndex)).dtor_masterKeyType).Equals((Dafny.Sequence<char>.FromString("aws-kms")))) {
            _1013_allKMS = false;
          }
          _1014_allKMSIndex = (_1014_allKMSIndex) + (BigInteger.One);
        }
        if (!(_1013_allKMS)) {
          _1008_skipCount = (_1008_skipCount) + (BigInteger.One);
        } else {
          TestVectorExterns.MasterKey _1015_masterKeyKMS;
          _1015_masterKeyKMS = (_1012_keysToTest).Select(BigInteger.Zero);
          KMSUtils.DefaultClientSupplier _1016_clientSupplier;
          var _nw14 = new KMSUtils.DefaultClientSupplier();
_nw14.__ctor();
          _1016_clientSupplier = _nw14;
          _46_KMSKeyring_Compile.KMSKeyring _1017_keyring;
          var _nw15 = new _46_KMSKeyring_Compile.KMSKeyring();
_nw15.__ctor(_1016_clientSupplier, Dafny.Sequence<Dafny.Sequence<char>>.FromElements(), @STL.Option<Dafny.Sequence<char>>.create_Some(((_1015_masterKeyKMS).dtor_key).dtor_keyID), Dafny.Sequence<Dafny.Sequence<char>>.FromElements());
          _1017_keyring = _nw15;
          _132_DefaultCMMDef_Compile.DefaultCMM _1018_cmm;
          var _nw16 = new _132_DefaultCMMDef_Compile.DefaultCMM();
_nw16.OfKeyring(_1017_keyring);
          _1018_cmm = _nw16;
          STL.Result<Dafny.Sequence<byte>> _1019_d;
STL.Result<Dafny.Sequence<byte>> _out132;
var _outcollector132 = _176_ESDKClient_Compile.__default.Decrypt((_1011_ciphertext).dtor_value, _1018_cmm);
_out132 = _outcollector132;
_1019_d = _out132;
          if ((_1019_d).is_Failure) {
            Dafny.Helpers.Print((_1009_toTest).dtor_testID);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(": FAILED\n"));
            _1006_failCount = (_1006_failCount) + (BigInteger.One);
          } else if (!((_1019_d).dtor_value).Equals(((_1010_plaintext).dtor_value))) {
            Dafny.Helpers.Print((_1009_toTest).dtor_testID);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(": FAILED\n"));
            _1006_failCount = (_1006_failCount) + (BigInteger.One);
          } else {
            _1007_passCount = (_1007_passCount) + (BigInteger.One);
          }
        }
        _1005_j = (_1005_j) + (BigInteger.One);
      }
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("Passed: "));
Dafny.Helpers.Print(_1007_passCount);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(" Failed: "));
Dafny.Helpers.Print(_1006_failCount);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(" Skipped: "));
Dafny.Helpers.Print(_1008_skipCount);
Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
    }
  }
} // end of namespace TestVectorExterns
namespace _module {






























} // end of namespace _module
