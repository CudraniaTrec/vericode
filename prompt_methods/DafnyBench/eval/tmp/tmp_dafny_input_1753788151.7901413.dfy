
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
{
  var r := 1;
  u := 1;
  while (r < n)
    invariant 1 <= r <= n
    invariant u == Factorial(r)
  {
    var v, s := u, 1;
    while (s < r + 1)
      invariant 1 <= s <= r + 1
      invariant u == v * s
      invariant v == Factorial(r)
    {
      u := u + v;
      s := s + 1;
    }
    assert u == v * (r + 1);
    assert v == Factorial(r);
    assert u == Factorial(r) * (r + 1);
    r := r + 1;
  }
  assert r == n ==> u == Factorial(n);
}

function abs(a: real) : real {if a>0.0 then a else -a}
