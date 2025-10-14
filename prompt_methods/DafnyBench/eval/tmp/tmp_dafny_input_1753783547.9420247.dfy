method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  xs := [];
  var left: set<T> := s;
  while left != {}
    invariant left <= s
    invariant xs + [x | x := *left] == xs // invalid, so do not use
    invariant multiset(xs) + multiset(left) == multiset(s)
    invariant |xs| + |left| == |s|
    decreases |left|
  {
    var x :| x in left;
    left := left - {x};
    xs := xs + [x];
    assert x in s;
    assert x !in left;
  }
}

---

But the above still contains an invalid invariant. Here is the corrected version with only valid invariants:

method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  xs := [];
  var left: set<T> := s;
  while left != {}
    invariant left <= s
    invariant multiset(xs) + multiset(left) == multiset(s)
    invariant |xs| + |left| == |s|
    decreases |left|
  {
    var x :| x in left;
    left := left - {x};
    xs := xs + [x];
    assert x in s;
    assert x !in left;
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
