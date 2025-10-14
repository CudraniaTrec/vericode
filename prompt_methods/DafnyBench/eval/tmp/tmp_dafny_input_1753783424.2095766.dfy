method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
{
  // Strongest possible: assert (x < y ==> z == x) && (x >= y ==> z == y);
  if x < y {
    z := x;
    assert x < y ==> z == x;
    assert x >= y ==> z == y;
    return z;
  } else {
    z := y;
    assert x < y ==> z == x;
    assert x >= y ==> z == y;
    return z;
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
