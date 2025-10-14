method ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  // No loop, but assert the postcondition for maximal annotation
  avg:= (a + b) / 2;
  assert avg == (a + b) / 2;
}
function abs(a: real) : real {if a>0.0 then a else -a}
