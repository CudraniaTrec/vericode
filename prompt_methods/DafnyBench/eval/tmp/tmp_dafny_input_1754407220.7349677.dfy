
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
{
  min := s[0];
  var j := 0;
  // Invariant: min is the smallest among s[0..i)
  for i := 1 to s.Length
    invariant 1 <= i <= s.Length
    invariant 0 <= j < i
    invariant min == s[j]
    invariant forall k :: 0 <= k < i ==> min <= s[k]
    invariant exists k :: 0 <= k < i && min == s[k]
  {
    if s[i] < min
    {
      min := s[i];
      j := i;
    }
    assert forall k :: 0 <= k < i+1 ==> min <= s[k];
    assert exists k :: 0 <= k < i+1 && min == s[k];
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
