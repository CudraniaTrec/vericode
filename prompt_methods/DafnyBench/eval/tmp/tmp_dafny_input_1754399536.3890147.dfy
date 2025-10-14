
method SwapBitvectors(X: bv8, Y: bv8) returns(x: bv8, y: bv8)
  ensures x==Y
  ensures y==X
{
  x, y := X, Y;

  // Invariant: x ^ y == X ^ Y
  // After first assignment: x = X ^ Y, y = Y
  x := x ^ y;
  assert x == X ^ Y;
  assert y == Y;

  // After second assignment: y = (X ^ Y) ^ Y = X, x = X ^ Y
  y := x ^ y;
  assert y == (X ^ Y) ^ Y;
  assert y == X;
  assert x == X ^ Y;

  // After third assignment: x = (X ^ Y) ^ X = Y, y = X
  x := x ^ y;
  assert x == (X ^ Y) ^ X;
  assert x == Y;
  assert y == X;
}

function abs(a: real) : real {if a>0.0 then a else -a}
