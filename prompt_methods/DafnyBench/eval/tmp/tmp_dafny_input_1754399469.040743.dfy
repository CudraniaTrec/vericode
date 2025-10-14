
method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{
  r:=x;
  q:=0;
  while y<=r
    invariant 0 <= r <= x
    invariant 0 <= q
    invariant q * y + r == x
    invariant y != 0
  {
    r:=r-y;
    q:=q+1;
    assert q * y + r == x;
    assert 0 <= r;
    assert 0 <= q;
  }
  assert q * y + r == x;
  assert 0 <= r < y;
  assert 0 <= q;
}

function abs(a: real) : real {if a>0.0 then a else -a}
