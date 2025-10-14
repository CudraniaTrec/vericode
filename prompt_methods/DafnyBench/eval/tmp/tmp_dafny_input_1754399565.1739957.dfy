method Triple (x:int) returns (r:int)
  ensures r==3*x
{
  // No loop or complex logic, so no invariants needed.
  // Strongest assertion before return:
  assert r == x*3;
  r:= x*3;
  assert r == 3*x;
}
function abs(a: real) : real {if a>0.0 then a else -a}
