method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
{
  if x < y {
    assert x < y;
    assert x <= y;
    z := x;
    assert x <= y ==> z == x;
    assert x > y ==> z == y;
    return x;
  } else {
    assert !(x < y);
    assert x >= y;
    z := y;
    assert x <= y ==> z == x;
    assert x > y ==> z == y;
    return y;
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
