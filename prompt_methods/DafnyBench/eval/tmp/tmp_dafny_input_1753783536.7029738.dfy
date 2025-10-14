
method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  xs := [];
  var left: set<T> := s;
  while left != {}
    invariant left <= s
    invariant xs + [x | x <- SetToSeq.left] == xs + [x | x in left]
    invariant multiset(xs) + multiset(left) == multiset(s)
    invariant xs.Length + |left| == |s|
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
