
method Swap(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
{
  x, y := X, Y;

  // At this point: x == X && y == Y
  assert x == X && y == Y;

  var tmp := x;
  // tmp == X
  assert tmp == X;

  x := y;
  // x == Y && tmp == X
  assert x == Y && tmp == X;

  y := tmp;
  // y == X && x == Y
  assert y == X && x == Y;
}

function abs(a: real) : real {if a>0.0 then a else -a}
