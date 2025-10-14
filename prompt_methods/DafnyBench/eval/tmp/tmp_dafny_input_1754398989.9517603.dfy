method ComputeAvg(a: int, b: int) returns (avg:int)
  ensures avg == (a+b)/2
{
  // No loop or complex computation, but add an assert to strengthen reasoning.
  assert avg == (a + b) / 2 by {
    // Direct assignment
  };
  avg:= (a + b) / 2;
  assert avg == (a + b) / 2;
}
function abs(a: real) : real {if a>0.0 then a else -a}
