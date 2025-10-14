method Triple (x:int) returns (r:int)
  ensures r==3*x
{
  r := x*3;
  assert r == 3*x;
}
function abs(a: real) : real {if a>0.0 then a else -a}
