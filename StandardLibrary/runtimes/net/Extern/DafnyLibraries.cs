// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.Numerics;
using _System;
using Dafny;


namespace DafnyLibraries {
   public partial class MutableMap<K, V>
   {
      private ConcurrentDictionary<K, V> m;
      public MutableMap() {
         m = new ConcurrentDictionary<K, V>();
      }

      public IMap<K, V> content() {
         var keyPairs = new List<IPair<K, V>>();
         foreach (var k in m.Keys) {
            keyPairs.Add(new Pair<K, V>(k, m[k]));
         }
         return Map<K, V>.FromCollection(keyPairs);
      }

      public void Put(K k, V v)
      {
         m[k] = v;
      }

      public Dafny.ISet<K> Keys()
      {
         var keys = m.Keys;
         return Set<K>.FromCollection(keys);
      }

      public bool HasKey(K k)
      {
         return m.ContainsKey(k);
      }

      public Dafny.ISet<V> Values()
      {
         var values= m.Values;
         return Set<V>.FromCollection(values);
      }

      public Dafny.ISet<_ITuple2<K, V>> Items()
      {
         var keyPairs = new List<_ITuple2<K, V>>();
         foreach (var k in m.Keys) {
            keyPairs.Add(new Tuple2<K, V>(k, m[k]));
         }
         return Set<_ITuple2<K,V>>.FromCollection(keyPairs);
      }

      public V Select(K k)
      {
         return m[k];
      }

      public void Remove(K k)
      {
         if (HasKey(k)) {
            var keypair = new KeyValuePair<K, V>(k, m[k]); 
            m.TryRemove(keypair);
         }
      }

      public BigInteger Size()
      {
         return new BigInteger(m.Count);
      }
   }
}
