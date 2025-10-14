
method SwapArithmetic(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X

{
  x, y := X, Y;

  // x == X, y == Y
  x := y - x;
  // x == Y - X, y == Y
  assert x + X == Y;
  y := y - x;
  // x == Y - X, y == Y - (Y - X) == X
  assert y == X;
  x := y + x;
  // x == X + (Y - X) == Y, y == X
  assert x == Y && y == X;
}

function abs(a: real) : real {if a>0.0 then a else -a}
