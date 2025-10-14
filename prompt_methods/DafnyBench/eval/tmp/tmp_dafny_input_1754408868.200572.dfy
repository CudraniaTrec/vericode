method nonZeroReturn(x: int) returns (y: int)
  ensures y != 0
{
  if x == 0 {
    assert x + 1 != 0;
    return x + 1;
  } else {
    assert -x != 0;
    return -x;
  }
}
method test() {
  var input := nonZeroReturn(-1);
}

function abs(a: real) : real {if a>0.0 then a else -a}
