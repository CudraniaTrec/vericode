function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{
  var i := 0;
  res := 1;
  while i < n
    invariant 0 <= i <= n
    invariant res == Expt(b, i)
  {
    res := res * b;
    i := i + 1;
    assert res == Expt(b, i);
  }
  assert i == n;
  assert res == Expt(b, n);
}

// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
{
  if a == 0 {
    assert Expt(x, 0) == 1;
    assert Expt(x, 0) * Expt(x, b) == Expt(x, b);
    assert Expt(x, 0 + b) == Expt(x, b);
  } else {
    distributive(x, a - 1, b);
    assert Expt(x, a) == x * Expt(x, a - 1);
    assert Expt(x, a) * Expt(x, b) == (x * Expt(x, a - 1)) * Expt(x, b);
    assert (x * Expt(x, a - 1)) * Expt(x, b) == x * (Expt(x, a - 1) * Expt(x, b));
    assert x * (Expt(x, a - 1) * Expt(x, b)) == x * Expt(x, (a - 1) + b);
    assert x * Expt(x, (a - 1) + b) == Expt(x, a + b);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
