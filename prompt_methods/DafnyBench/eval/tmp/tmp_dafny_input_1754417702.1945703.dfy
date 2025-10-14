// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91;
{
  var y1 := x;
  var y2 := 1;
  while (true)
    invariant y2 >= 1
    invariant proveFunctionalPostcondition ==> (
      (y2 == 1 ==> y1 - 10 == if y1 > 101 then y1 - 10 else 91)
    )
    decreases if y1 > 100 then y2 else 101 - y1, y2
  {
    if (y1 > 100) {
      if (y2 == 1) {
        break;
      } else {
        y1 := y1 - 10;
        y2 := y2 - 1;
      }
    } else {
      y1 := y1 + 11;
      y2 := y2 + 1;
    }
  }
  z := y1 - 10;
}

method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
{
  var y1 := x1;
  var y2 := x2;
  while (y1 != y2)
    invariant 1 <= y1 && 1 <= y2
    invariant gcd(x1, x2) == gcd(y1, y2)
    decreases if y1 > y2 then y1 - y2 else y2 - y1
  {
    while (y1 > y2)
      invariant y1 > 0 && y2 > 0
      invariant y1 >= y2
      invariant gcd(x1, x2) == gcd(y1, y2)
      decreases y1 - y2
    {
      y1 := y1 - y2;
    }
    while (y2 > y1)
      invariant y1 > 0 && y2 > 0
      invariant y2 >= y1
      invariant gcd(x1, x2) == gcd(y1, y2)
      decreases y2 - y1
    {
      y2 := y2 - y1;
    }
  }
}

function gcd(a: int, b: int): int
  requires 1 <= a && 1 <= b
{
  if a == b then a else if a > b then gcd(a - b, b) else gcd(a, b - a)
}

method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M;
  requires X != null && M == X.Length0 && M == X.Length1;
  modifies X;
{
  var y := X[1-1,1-1];
  var a := 1;
  while (a != M)
    invariant 1 <= a <= M
    decreases M - a
  {
    var b := a + 1;
    while (b != M+1)
      invariant a+1 <= b <= M+1
      decreases M+1 - b
    {
      var c := M;
      while (c != a)
        invariant a < c <= M
        decreases c - a
      {
        assume X[a-1,a-1] != 0;
        X[b-1, c-1] := X[b-1,c-1] - X[b-1,a-1] / X[a-1,a-1] * X[a-1,c-1];
        c := c - 1;
      }
      b := b + 1;
    }
    a := a + 1;
    y := y * X[a-1,a-1];
  }
  z := y;
}

function abs(a: real) : real {if a>0.0 then a else -a}
