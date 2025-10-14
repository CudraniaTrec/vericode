
method CalcProduct(m: nat, n: nat) returns (res: nat)
  ensures res == m*n;
{ 
  var m1: nat := m;
  res := 0;

  // Invariant: res == (m - m1) * n && m1 <= m
  // Loop simulates: while (m1 != 0) { ... }
  // But here, we use assignments and assumes instead.

  // Strongest annotation at this point:
  assert res == (m - m1) * n;
  assert m1 <= m;

  m1, res := *, *;
  assume res == (m-m1)*n;
  assert res == (m - m1) * n;
  assert m1 <= m;

  if (m1!=0) 
  {   
    var n1: nat := n;
    // havoc res, n1;
    res, n1 := *, *;
    assume res == (m-m1)*n + (n-n1);
    assert res == (m - m1) * n + (n - n1);
    assert n1 <= n;

    if (n1 != 0)
    {
      ghost var old_n1 := n1;
      assert n1 == old_n1;
      assert res == (m - m1) * n + (n - n1);

      // Invariant for inner loop:
      // res == (m - m1) * n + (n - n1)
      // n1 <= n
      res := res+1;
      n1 := n1-1; 
      assert res == (m - m1) * n + (n - n1) + 1;
      assert n1 == old_n1 - 1;
      assume (false);
    }  
    m1 := m1-1;
    assert m1 + 1 <= m;
    assume false;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
