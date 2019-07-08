include "../Util/StandardLibrary.dfy"
include "../Util/Sort.dfy"

module EncCtx {
    import opened StandardLibrary
    module S refines Sort {
        import opened StandardLibrary
        import O = SeqByteKeysOrder
    }

    // Serialization format is:
    // L : length of everything below 
    // N : number of pairs
    // for each pair:
        // length of key
        // key
        // length of val
        // val

    // TODO maintain UTF8-encoding
    predicate enc_ctx_sorted_nodup (x : seq<(seq<byte>, seq<byte>)>) { S.O.compat_mset(multiset(x)) && S.SeqSorted(x) }
    type EncCtx = x : seq<(seq<byte>, seq<byte>)> | enc_ctx_sorted_nodup(x)
    
    module Ser {
        import opened StandardLibrary
        predicate method wf_ser_enc_ctx_head (e : seq<(seq<byte>, seq<byte>)> ) { 
            sum(e, (p : (seq<byte>, seq<byte>)) => |p.0| + |p.1| + 4) + 4 <= UINT16_MAX // able to serialize length of serialization 
            && |e| <= UINT16_MAX // able to serialize number of pairs
        }

        lemma wf_ser_enc_ctx_head_perm (e : seq<(seq<byte>, seq<byte>)>, e' : seq<(seq<byte>, seq<byte>)>)
            requires multiset(e) == multiset(e')
            ensures wf_ser_enc_ctx_head(e) <==> wf_ser_enc_ctx_head(e') 
        {
            eq_multiset_eq_len(e, e');
            sum_perm(e, e', (p : (seq<byte>, seq<byte>)) => |p.0| + |p.1| + 4);
        }

        predicate method wf_ser_enc_ctx_body (e : seq<(seq<byte>, seq<byte>)> ) {
            forall p :: p in e ==> |p.0| <= UINT16_MAX && |p.1| <= UINT16_MAX // able to serialize each pair
        }

        predicate method wf_ser_enc_ctx (e : seq<(seq<byte>, seq<byte>)>) { wf_ser_enc_ctx_body(e) && wf_ser_enc_ctx_head(e) }

        lemma wf_ser_enc_ctx_body_perm(e : seq<(seq<byte>, seq<byte>)>, e' : seq<(seq<byte>, seq<byte>)>) 
            requires multiset(e) == multiset(e')
            ensures wf_ser_enc_ctx_body(e) <==> wf_ser_enc_ctx_body(e') 
        {
            assert (forall p :: p in e <==> p in multiset(e));
            assert (forall p :: p in e <==> p in e');
        }


        predicate ser_space_for (s : seq<(seq<byte>, seq<byte>)>, kl : nat, vl : nat) {
            forall k, v :: |k| == kl ==> |v| == vl ==> wf_ser_enc_ctx_body([(k,v)] + s) && wf_ser_enc_ctx_head([(k,v)] + s)
        }

        lemma ser_space_forP (s : seq<(seq<byte>, seq<byte>)>, kl : nat, vl : nat)
            requires forall p :: p in s ==> |p.0| <= UINT16_MAX && |p.1| <= UINT16_MAX
            requires sum(s, (p : (seq<byte>, seq<byte>)) => |p.0| + |p.1| + 4) + 4 <= UINT16_MAX - (kl + vl + 4)
            requires |s| <= UINT16_MAX - 1
            requires kl <= UINT16_MAX && vl <= UINT16_MAX
            ensures ser_space_for(s, kl, vl) 
        {
            forall k, v | |k| == kl && |v| == vl ensures wf_ser_enc_ctx_body([(k,v)] + s) && wf_ser_enc_ctx_head([(k,v)] + s) {
                assert |[(k,v)] + s| <= UINT16_MAX;
                calc {
                    sum([(k,v)] + s, (p : (seq<byte>, seq<byte>)) => |p.0| + |p.1| + 4) + 4
                    ==
                    sum(s, (p : (seq<byte>, seq<byte>)) => |p.0| + |p.1| + 4) + |k| + |v| + 4
                    <= UINT16_MAX;
                }
                assert sum([(k,v)] + s, (p : (seq<byte>, seq<byte>)) => |p.0| + |p.1| + 4) + 4 <= UINT16_MAX;
            }
        }


        predicate serializeable(s : seq<(seq<byte>, seq<byte>)>) 
        {
            wf_ser_enc_ctx_body(s) && wf_ser_enc_ctx_head(s)
        }

        lemma serializeable_perm (e : seq<(seq<byte>, seq<byte>)>, e' : seq<(seq<byte>, seq<byte>)>) 
            requires multiset(e) == multiset(e')
            ensures serializeable(e) == serializeable(e') 
        {
            wf_ser_enc_ctx_body_perm(e, e');
            wf_ser_enc_ctx_head_perm(e, e');
        }

        function method ser_enc_ctx_pair(c : (seq<byte>, seq<byte>)) : (res : seq<byte>)
            requires wf_ser_enc_ctx_body([c])
            ensures |res| == |c.0| + |c.1| + 4
        {
            var keylen := ser_uint16(|c.0| as uint16);
            var val_len := ser_uint16(|c.1| as uint16);
            [keylen.0, keylen.1] + c.0 + [val_len.0, val_len.1] + c.1
        }

        function method ser_enc_ctx_body(c : seq<(seq<byte>, seq<byte>)>) : (res : seq<byte>)
            requires wf_ser_enc_ctx_body(c)
            ensures |res| == sum(c, (p : (seq<byte>, seq<byte>)) => |p.0| + |p.1| + 4)
        {
            if c == [] then [] else ser_enc_ctx_pair(c[0]) + ser_enc_ctx_body(c[1..])
        }

        function method ser_enc_ctx(c : seq<(seq<byte>, seq<byte>)>) : (s : seq<byte>)
            requires wf_ser_enc_ctx_body(c)
            requires wf_ser_enc_ctx_head(c)
            ensures |s| == sum(c, (p : (seq<byte>, seq<byte>)) => |p.0| + |p.1| + 4) + 4
        {
            var ser_body := ser_enc_ctx_body(c);
            var ser_numpairs := ser_uint16(|c| as uint16);
            var ser_len := ser_uint16((|ser_body| + 2) as uint16);
            [ser_len.0, ser_len.1, ser_numpairs.0, ser_numpairs.1] + ser_body
        }

    }

    method MkEncCtx (s : seq<(seq<byte>, seq<byte>)>) returns (o : EncCtx)
        requires uniq_fst(s)
        ensures multiset(s) == multiset(o)
    {
        var a : array<(seq<byte>, seq<byte>)> := new [|s|];
        forall i | 0 <= i < a.Length {
            a[i] := s[i];
        }
        assert (a[..] == s);
        uniq_fst_idxP(s);
        compatP(s);
        assert (S.O.compat_mset(multiset(s)));
        S.InsertionSort(a);
        o := a[..];
    }

    method InsertEncCtx (s : EncCtx, k : seq<byte>, v : seq<byte>) returns (o : EncCtx)
        requires forall j :: j in s ==> j.0 != k
        ensures multiset(o) == multiset{(k,v)} + multiset(s)
        ensures Ser.ser_space_for(s, |k|, |v|) ==> Ser.serializeable(o)
        ensures k in keys(o)
        ensures lookup(o, k) == v
    {
        var a : array<(seq<byte>, seq<byte>)> := new [|s| + 1];
        forall i | 1 <= i < |s| + 1 {
            a[i] := s[i - 1];
        }
        a[0] := (k,v);
        assert (a[..] == [(k,v)] + s);
        notin_keys_compat_mset(s, k, v);
        S.InsertionSort(a);
        o := a[..];
        assert (multiset(o) == multiset(s) + multiset{(k,v)});
        assert ((k,v) in multiset(o));
        assert ((k,v) in o);
        in_keysP(o, k);
        if Ser.ser_space_for(s, |k|, |v|) {
            Ser.serializeable_perm(o, [(k,v)] + s);
        }
    }

    lemma uniq_keys (c : EncCtx)
        ensures forall j, i :: 0 <= j < i < |c| ==> c[i].0 != c[j].0 
    {
        var s := multiset(c);
        assert (forall i, j :: i in s ==> j in s ==> i != j ==> i.0 != j.0); 
        forall j, i | 0 <= j < i < |c| ensures c[i] != c[j] && c[i].0 != c[j].0 {
            assert c[i] in s;
            assert c[j] in s;
            if c[i] == c[j] {
                multiset_of_seq_dup(c, j, i);
            }
        }
    }
    
    lemma enc_ctx_uniq (c : EncCtx)
        ensures uniq(c) {
        uniq_keys(c);
        uniq_idxP(c);
    }

    lemma compatP (s : seq<(seq<byte>, seq<byte>)>)
        requires forall i, j :: 0 <= i < j < |s| ==> s[i].0 != s[j].0
        ensures S.O.compat_mset(multiset(s)) {
        uniq_idxP(s);
        assert (uniq(s));
        uniq_multisetP(s);
    }
    

    function method keys(c : seq<(seq<byte>, seq<byte>)>) : seq<seq<byte>> {
        if c == [] then [] else [c[0].0] + keys(c[1..])
    }

    lemma notin_keysP (c : seq<(seq<byte>, seq<byte>)>, x : seq<byte>) 
    ensures (x !in keys(c)) <==> (forall j :: j in c ==> j.0 != x) {

    }

    lemma in_keysP (c : seq<(seq<byte>, seq<byte>)>, x : seq<byte>)
        ensures
        (x in keys(c)) <==> (exists j :: j in c && j.0 == x) {

    }

       

    lemma notin_keys_compat_mset(s : EncCtx, k : seq<byte>, v : seq<byte>)
    requires forall j :: j in s ==> j.0 != k
    ensures S.O.compat_mset(multiset(s) + multiset{(k,v)}) {

    }

    function method lookup(c : seq<(seq<byte>, seq<byte>)>, k : seq<byte>) : (s : seq<byte>)
        requires k in keys(c)
        ensures (k,s) in c 
    {
        assert(|c| > 0);
        if c[0].0 == k then c[0].1 
        else lookup(c[1..], k)
    }




    lemma enc_ctx_notin_tail (s : EncCtx)
        requires |s| > 0
        ensures s[0] !in s[1..] {
            enc_ctx_uniq(s);
        }

    lemma enc_ctx_tail (s : EncCtx)
        requires |s| > 0
        ensures S.O.compat_mset(multiset(s[1..])) && S.SeqSorted(s[1..]) {
            assert s == [s[0]] + s[1..];
            assert multiset(s[1..]) == multiset(s) - multiset{s[0]};
        }

}