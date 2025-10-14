method Triple (x:int) returns (r:int)
  ensures r==3*x
{
  var y:= x*2;
  assert y == 2*x;
  r := y+x;
  assert r == y + x;
  assert r == 2*x + x;
  assert r == 3*x;
}
function abs(a: real) : real {if a>0.0 then a else -a}
