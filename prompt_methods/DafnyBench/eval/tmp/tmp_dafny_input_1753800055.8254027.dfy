
// problem 6:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXXX

ghost function f(n: int): int {
  if n <= 0 then 1 else n + f(n-1)*f(n-2)
}

ghost function fSum(n: nat): int {
 // give the body of this function
  // it should return Sum(i: 0<=i < n: f(i))
  if n <= 0 then 0 else f(n-1) + fSum(n-1)
}

method problem6(n:nat) returns (a: int)
ensures a == fSum(n)
{
  a := 0;
  var k := 0;
  var x := 1;
  var y := 2;
  while k < n
    invariant 0 <= k <= n
    invariant a == fSum(k)
    invariant x == f(k)
    invariant y == f(k+1)
  {
    k := k + 1;
    a := a + x;

    x, y := y, k+1 + x*y;    
  }
  assert k == n;
  assert a == fSum(n);
}

function abs(a: real) : real {if a>0.0 then a else -a}
