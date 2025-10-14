
method CalDiv() returns (x:int, y:int)
  ensures x==191/7
  ensures y==191%7
{

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= x <= 191/7 + 1
    invariant y == 191 - 7*x
    invariant 0 <= y <= 191
  {
    x := x+1;
    y:=191-7*x;
  }
  assert y < 7;
}

function abs(a: real) : real {if a>0.0 then a else -a}
