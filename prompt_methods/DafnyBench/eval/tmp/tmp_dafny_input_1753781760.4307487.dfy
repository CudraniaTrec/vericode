method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    assert x < 0;
    assert -x > 0 || x == -x; // -x is non-negative
    return -x;
  } else {
    assert x >= 0;
    return x;
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
