
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
{
  var idx := 0;
  while (idx < Array.Length)
    invariant 0 <= idx <= Array.Length
    invariant multiset(old(Array[..])) == multiset(Array[..])
    invariant forall i, j :: 0 <= i < idx <= j < Array.Length ==> Array[i] <= Array[j]
  {
    var minIndex := idx;
    var idx' := idx + 1;
    while (idx' < Array.Length)
      invariant idx + 1 <= idx' <= Array.Length
      invariant idx <= minIndex < Array.Length
      invariant forall k :: idx <= k < idx' ==> Array[minIndex] <= Array[k]
      invariant forall i, j :: 0 <= i < idx <= j < Array.Length ==> Array[i] <= Array[j]
      invariant multiset(old(Array[..])) == multiset(Array[..])
    {
      if (Array[idx'] < Array[minIndex]) {
        minIndex := idx';
      }
      idx' := idx' + 1;
    }
    Array[idx], Array[minIndex] := Array[minIndex], Array[idx];
    assert multiset(old(Array[..])) == multiset(Array[..]);
    idx := idx + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
