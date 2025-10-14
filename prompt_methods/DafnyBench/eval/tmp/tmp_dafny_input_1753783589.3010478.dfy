
method SwapBitvectors(X: bv8, Y: bv8) returns(x: bv8, y: bv8)
  ensures x==Y
  ensures y==X
{
  x, y := X, Y;

  // x = X, y = Y
  assert x == X && y == Y;

  x := x ^ y;
  // x = X ^ Y, y = Y
  assert x == X ^ Y && y == Y;

  y := x ^ y;
  // x = X ^ Y, y = (X ^ Y) ^ Y = X
  assert x == X ^ Y && y == X;

  x := x ^ y;
  // x = (X ^ Y) ^ X = Y, y = X
  assert x == Y && y == X;
}

function abs(a: real) : real {if a>0.0 then a else -a}
