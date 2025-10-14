method SwapSimultaneous(X: int, Y: int) returns(x: int, y: int)
  ensures x==Y
  ensures y==X
{
  x, y := X, Y;
  assert x == X && y == Y;
  x, y := y, x;
  assert x == Y && y == X;
}
function abs(a: real) : real {if a>0.0 then a else -a}
