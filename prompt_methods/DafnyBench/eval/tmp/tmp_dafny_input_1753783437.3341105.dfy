method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  // After assignment, more == x + y
  more := x + y;
  assert more == x + y;

  // After assignment, less == x - y
  less := x - y;
  assert less == x - y;
}
function abs(a: real) : real {if a>0.0 then a else -a}
