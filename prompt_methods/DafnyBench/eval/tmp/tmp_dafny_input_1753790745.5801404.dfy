method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
{
  if a > b {
    // a > b, so a >= b holds, so ensures a >= b ==> c == a
    // c will be a
    // Also, max(a, b) == a
    assert a >= b;
    return a;
  } else {
    // b >= a, so ensures b >= a ==> c == b
    // c will be b
    // Also, max(a, b) == b
    assert b >= a;
    return b;
  }
}

method MaxTest() {
  var low := 1;
  var high := 10;
  var v := Max(low, high);
  assert v == high;
  assert v == max(low, high);
}

function max(a: int, b: int): int
{
  if a > b then a else b
}

method maxTest() {
  var x := 5;
  var y := 7;
  var m := max(x, y);
  assert m == 7;
  assert m == x || m == y;
}

function abs(a: real) : real {if a>0.0 then a else -a}
