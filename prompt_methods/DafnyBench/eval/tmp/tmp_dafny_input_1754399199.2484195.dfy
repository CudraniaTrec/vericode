method DoubleQuadruple(x: int) returns (a: int, b: int)
  ensures a == 2 * x && b == 4 * x
{
  a := 2 * x;
  assert a == 2 * x;
  b := 2 * a;
  assert b == 2 * (2 * x);
  assert b == 4 * x;
}
function abs(a: real) : real {if a>0.0 then a else -a}
