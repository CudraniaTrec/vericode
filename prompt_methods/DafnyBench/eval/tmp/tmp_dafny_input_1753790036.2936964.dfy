method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
{
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
}

method TestingAbs()
{
  var w := Abs(4);
  assert w == 4;
  assert w >= 0;
  var v := Abs(3);
  assert v == 3;
  assert v >= 0;
}

method TestingAbs2()
{
  var v := Abs(3); 
  assert v == 3;
  assert v >= 0;
}



// Exercise 1. Write a test method that calls your Max method from Exercise 0 and then asserts something about the result.
// Use your code from Exercise 0
method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
{
  c := a;
  if b > c {
    c := b;
  }
}

method TestingMax() {
  var a := 3;
  var b := 2;
  var c := Max(a, b);
  assert c == a;
  assert c >= a;
  assert c >= b;
}
function abs(a: real) : real {if a>0.0 then a else -a}
