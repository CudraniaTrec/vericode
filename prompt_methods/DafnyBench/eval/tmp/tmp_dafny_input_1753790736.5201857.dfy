
method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
{
  // Strongest postcondition: c == max(a, b)
  assert c == max(a, b);
  if a > b {
    assert a > b;
    assert max(a, b) == a;
    return a;
  } else {
    assert b >= a;
    assert max(a, b) == b;
    return b;
  }
}

method MaxTest() {
  var low := 1;
  var high := 10;
  var v := Max(low, high);
  assert v == max(low, high);
  assert v == high;
  assert v >= low && v >= high - 1;
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
  assert m == max(x, y);
  assert m >= x && m >= y;
  assert m == x || m == y;
}

function abs(a: real) : real {if a>0.0 then a else -a}
