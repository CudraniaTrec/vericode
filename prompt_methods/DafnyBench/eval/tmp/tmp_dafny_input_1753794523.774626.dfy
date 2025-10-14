
method Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
{
  var x := xInit;
  z := x * y;
  
  while x > 0
    invariant x >= 0
    invariant z == x * y
    invariant x <= xInit
  {
    x := x - 1;
    z := z - y;
    assert z == x * y;
  }
  assert x == 0;
  assert z == 0;
}

function abs(a: real) : real {if a>0.0 then a else -a}
