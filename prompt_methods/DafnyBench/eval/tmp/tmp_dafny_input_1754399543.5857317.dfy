method Swap(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
{
  x, y := X, Y;

  // At this point: x == X && y == Y
  assert x == X && y == Y;

  var tmp := x;
  // tmp == X && x == X && y == Y
  assert tmp == X && x == X && y == Y;

  x := y;
  // x == Y && tmp == X && y == Y
  assert x == Y && tmp == X && y == Y;

  y := tmp;
  // x == Y && y == X
  assert x == Y && y == X;
}

function abs(a: real) : real {if a>0.0 then a else -a}
