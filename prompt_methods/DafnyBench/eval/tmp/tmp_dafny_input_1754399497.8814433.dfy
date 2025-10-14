
method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  xs := [];
  var left: set<T> := s;
  while left != {}
    invariant left <= s
    invariant xs + [x | x <- left] <= s
    invariant xs + [x | x <- left] == xs + left
    invariant multiset(xs) + multiset(left) == multiset(s)
    decreases |left|
  {
    var x :| x in left;
    left := left - {x};
    xs := xs + [x];
    assert x in s;
    assert x !in left;
  }
  assert left == {};
  assert multiset(xs) == multiset(s);
}

function abs(a: real) : real {if a>0.0 then a else -a}
