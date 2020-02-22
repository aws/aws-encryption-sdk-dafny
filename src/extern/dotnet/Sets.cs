using System;
using System.Linq;
using System.Collections.Generic;

namespace Sets {

  public partial class __default {
      public static Dafny.Sequence<Dafny.Sequence<T>> SetToOrderedSequence<T>(Dafny.Set<Dafny.Sequence<T>> set, Func<T,T,bool> less) {
          Dafny.Sequence<T>[] itemArray = set.Elements.ToArray();
          IComparer<Dafny.Sequence<T>> lexicographicComapre = new LexicographicComparer<T>(less);
          Array.Sort(itemArray, lexicographicComapre);
          return Dafny.Sequence<Dafny.Sequence<T>>.FromElements(itemArray);
      }
  }

  // Lexicographically compares two dafny sequences according to a given
  // isLessThan function
  public class LexicographicComparer<T> : Comparer<Dafny.Sequence<T>>  {
      private Func<T,T,bool> isLessThan;

      public LexicographicComparer(Func<T,T,bool> isLessThan) {
        this.isLessThan = isLessThan;
      }

      public override int Compare(Dafny.Sequence<T> x, Dafny.Sequence<T> y)  {
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
