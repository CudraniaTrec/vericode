
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
{
  min := s[0];
  var idx: int := 0;
  for i := 1 to s.Length
    invariant 1 <= i <= s.Length
    invariant 0 <= idx < i
    invariant min == s[idx]
    invariant forall j :: 0 <= j < i ==> min <= s[j]
    invariant exists j :: 0 <= j < i && min == s[j]
  {
    if s[i] < min
    {
      min := s[i];
      idx := i;
    }
  }
  // After the loop: i == s.Length
  // min == s[idx], 0 <= idx < s.Length
  // forall j :: 0 <= j < s.Length ==> min <= s[j]
  // exists j :: 0 <= j < s.Length && min == s[j]
  assert forall i :: 0 <= i < s.Length ==> min <= s[i];
  assert exists i :: 0 <= i < s.Length && min == s[i];
}

function abs(a: real) : real {if a>0.0 then a else -a}
