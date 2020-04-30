include "Orders.dfy"
  
module {:extern "STLSorting"} StandardLibrary.Sorting {
  export
    provides SelectionSort
    provides Orders

  import Orders
    
  /*
   * Selection sort
   */
  
  method SelectionSort<Data>(a: array<Data>, below: (Data, Data) -> bool)
    requires Orders.Transitive(below) && Orders.Connected(below)
    modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i, j :: 0 <= i < j < a.Length ==> below(a[i], a[j])
  {
    var m := 0;
    while m < a.Length
      invariant 0 <= m <= a.Length
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall i, j :: 0 <= i < j < m ==> below(a[i], a[j])
      invariant forall i, j :: 0 <= i < m <= j < a.Length ==> below(a[i], a[j])
    {
      // pick mindex to be the index of the smallest element in a[m..]
      var mindex, n := m, m + 1;
      while n < a.Length
        invariant m <= mindex < n <= a.Length
        invariant forall i :: m <= i < n ==> below(a[mindex], a[i])
      {
        if !below(a[mindex], a[n]) {
          mindex := n;
        }
        n := n + 1;
      }
      a[m], a[mindex] := a[mindex], a[m];
      m := m + 1;
    }
  }
}
