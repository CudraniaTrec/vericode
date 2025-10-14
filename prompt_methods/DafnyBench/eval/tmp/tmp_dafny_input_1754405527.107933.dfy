method Max(a: int, b: int) returns (c: int)
  ensures a >= b ==> c == a
  ensures b >= a ==> c == b
{
  // Strongest postcondition: c == max(a, b)
  // Assert that the result is indeed the maximum
  if a > b {
    c := a;
    assert c == max(a, b);
    return a;
  } else {
    c := b;
    assert c == max(a, b);
    return b;
  }
}

method MaxTest() {
  var low := 1;
  var high := 10;
  var v := Max(low, high);
  // Assert that v is the maximum of low and high
  assert v == max(low, high);
  assert v == high;
  assert v >= low && v >= high;
}

function max(a: int, b: int): int
{
  if a > b then a else b
}

method maxTest() {
  // Test some values
  var x := 42;
  var y := 17;
  var m := max(x, y);
  assert (x > y ==> m == x);
  assert (y >= x ==> m == y);
  assert m == max(x, y);
}
function abs(a: real) : real {if a>0.0 then a else -a}
