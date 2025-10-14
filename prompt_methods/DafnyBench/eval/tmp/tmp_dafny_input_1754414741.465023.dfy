
method CalcProduct(m: nat, n: nat) returns (res: nat)
  ensures res == m*n;
{ 
  var m1: nat := m;
  res := 0;

  // Loop to compute the product
  while (m1 != 0)
    invariant 0 <= m1 <= m
    invariant res == (m - m1) * n
  {
    var n1: nat := n;
    var r: nat := 0;

    // Inner loop to add n to res
    while (n1 != 0)
      invariant 0 <= n1 <= n
      invariant r == n - n1
    {
      r := r + 1;
      n1 := n1 - 1;
      assert r <= n;
    }
    res := res + r;
    m1 := m1 - 1;
    assert res == (m - m1) * n;
  }
  assert res == m * n;
}

function abs(a: real) : real {if a>0.0 then a else -a}
