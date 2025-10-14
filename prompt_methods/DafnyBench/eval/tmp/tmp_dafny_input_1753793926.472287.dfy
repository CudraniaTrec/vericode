// flips (i.e., reverses) array elements in the range [0..num]
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// ensures multiset(a[..]) == old(multiset(a[..]))
{
  var tmp:int;
  var i := 0;
  var j := num;
  while (i < j)
    // invariant 0 <= i <= j+1 <= num+1
    // invariant forall k :: 0 <= k < i ==> a[k] == old(a[num - k])
    // invariant forall k :: j < k <= num ==> a[k] == old(a[num - k])
    // invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    // invariant forall k :: num < k < a.Length ==> a[k] == old(a[k])
  {
    assert 0 <= i < a.Length;
    assert 0 <= j < a.Length;
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
  // After the loop: i >= j
  // For odd-length, i == j; for even-length, i == j+1
  // All a[0..num] have been reversed
  // All a[num+1..a.Length-1] are unchanged
}

function abs(a: real) : real {if a>0.0 then a else -a}
