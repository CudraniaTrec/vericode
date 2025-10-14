
method CalcProduct(m: nat, n: nat) returns (res: nat)
  ensures res == m*n;
{ 
  var m1: nat := m;
  res := 0;

  // Simulate: while (m1 != 0) { ... }
  // Strongest invariants for this loop:
  // res == (m - m1) * n && m1 <= m

  while (m1 != 0)
    invariant m1 <= m
    invariant res == (m - m1) * n
  {
    var n1: nat := n;
    var r: nat := 0;

    // Inner loop: while (n1 != 0) { r := r + 1; n1 := n1 - 1; }
    while (n1 != 0)
      invariant n1 <= n
      invariant r == n - n1
    {
      r := r + 1;
      n1 := n1 - 1;
    }
    // After inner loop: r == n, n1 == 0

    res := res + r;
    m1 := m1 - 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
