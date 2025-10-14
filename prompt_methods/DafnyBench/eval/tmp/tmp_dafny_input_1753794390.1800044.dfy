
// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.
method SelectionSort(a: array<int>)
  modifies a
  // Ensures the final array is sorted in ascending order
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // Ensures that the final array has the same elements as the initial array
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := 0;
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant forall i :: 0 <= i < n ==> forall j :: n <= j < a.Length ==> a[i] <= a[j]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var mindex, m := n, n;
    while m != a.Length
      invariant n <= m <= a.Length
      invariant n <= mindex < a.Length
      invariant forall k :: n <= k < m ==> a[mindex] <= a[k]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    // Swaps the first element of the unsorted array with the current smallest element
    // in the unsorted part if it is smaller
    if a[mindex] < a[n] {
      a[mindex], a[n] := a[n], a[mindex];
      assert multiset(a[..]) == old(multiset(a[..]));
    }
    n := n + 1;
  }  
}

function abs(a: real) : real {if a>0.0 then a else -a}
