
method plus_one (x: int) returns (r:int)
  requires x >= 0;
  ensures r == x + 1;
{
  return x+1;
}

method add_by_one (x:int, y:int) returns (r:int)
{
  assume (y >= 0);
  var i:int := 0;
  r := x;

  // Loop to add 1 to r, y times
  while (i < y)
    invariant 0 <= i <= y;
    invariant r == x + i;
    decreases y - i;
  {
    r := r + 1;
    i := i + 1;
  }

  // At this point, i == y and r == x + y
  assert i == y;
  assert r == x + y;

  return r;
}

function abs(a: real) : real {if a>0.0 then a else -a}
