// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Linq;
using System.Collections.Generic;

namespace Sets {

  public partial class __default {
      public static Dafny.ISequence<Dafny.ISequence<T>> SetToOrderedSequence<T>(Dafny.ISet<Dafny.ISequence<T>> set, Func<T,T,bool> less) {
          Dafny.ISequence<T>[] itemArray = set.Elements.ToArray();
          IComparer<Dafny.ISequence<T>> lexicographicComapre = new LexicographicComparer<T>(less);
          Array.Sort(itemArray, lexicographicComapre);
          return Dafny.Sequence<Dafny.ISequence<T>>.FromElements(itemArray);
      }
      // This is to facilitate moving the above from a `method` to a `function method` in Dafny.
      public static Dafny.ISequence<Dafny.ISequence<T>> SetToOrderedSequence2<T>(Dafny.ISet<Dafny.ISequence<T>> set, Func<T,T,bool> less) {
          return SetToOrderedSequence(set, less);
      }
      public static Dafny.ISequence<T> SetToSequence<T>(Dafny.ISet<T> set) {
          return Dafny.Sequence<T>.FromElements(set.Elements.ToArray());
      }
  }

  // Lexicographically compares two dafny sequences according to a given
  // isLessThan function
  public class LexicographicComparer<T> : Comparer<Dafny.ISequence<T>>  {
      private Func<T,T,bool> isLessThan;

      public LexicographicComparer(Func<T,T,bool> isLessThan) {
        this.isLessThan = isLessThan;
      }

      public override int Compare(Dafny.ISequence<T> x, Dafny.ISequence<T> y)  {
          if (x == null || y == null)
              return Default.Compare(x, y);
          T[] xArr = x.Elements;
          T[] yArr = y.Elements;

          for (int i = 0; i < xArr.Length && i < yArr.Length; i++) {
              bool xLessThanAtIndex = isLessThan(xArr[i], yArr[i]);
              if (xLessThanAtIndex) {
                  return -1;
              }

              bool yLessThanAtIndex = isLessThan(yArr[i], xArr[i]);
              if (yLessThanAtIndex) {
                  return 1;
              }
          }

          // Reached the end of one array. Either they are equal, or the
          // one which is shorter should be considered "less than"
          return xArr.Length.CompareTo(yArr.Length);
      }
   }
}
