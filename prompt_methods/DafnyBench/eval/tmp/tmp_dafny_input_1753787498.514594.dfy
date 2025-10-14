
method FindMax(a: array<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
  requires a.Length > 0
  ensures 0<= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  // Fill in the body that calculates the INDEX of the maximum.
  i := 0;
  var index := 1;
  while index < a.Length
    invariant 1 <= index <= a.Length
    invariant 0 <= i < index
    invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
  {
    if a[index] > a[i] {i:= index;}
    index := index + 1;
  }
  // At this point, index == a.Length
  // i is the index of the maximum value in a[0..a.Length-1]
  assert 0 <= i < a.Length;
  assert forall k :: 0 <= k < a.Length ==> a[k] <= a[i];
}

function abs(a: real) : real {if a>0.0 then a else -a}
