iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
    invariant |xs| == i
    invariant forall j :: 0 <= j < i ==> xs[j] == start + j
    decreases 10 - i
  {
    x := start + i;
    yield;
    i := i + 1;
  }
}

method Main() {
  var i := new Gen(30);
  while true
    decreases *
  {
    var m := i.MoveNext();
    if (!m) {break; }
    print i.x;
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
