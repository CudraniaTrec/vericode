function max(x:nat, y:nat) : nat
{
  if (x < y) then y else x
}

method slow_max(a: nat, b: nat) returns (z: nat)
  ensures z == max(a, b)
{
  z := 0;
  var x := a;
  var y := b;
  while (z < x && z < y)
    invariant 0 <= z <= a && 0 <= z <= b
    invariant x + z == a
    invariant y + z == b
    invariant x >= 0 && y >= 0
    invariant x <= a && y <= b
    invariant x - y == a - b
  {
    z := z + 1;
    x := x - 1;
    y := y - 1;
  }

  assert x == 0 || y == 0;
  // At this point, either x == 0 or y == 0, and x + z == a, y + z == b

  if (x <= y) { 
    z := b;
    assert z == max(a, b);
    return z;
  }
  else { 
    z := a;
    assert z == max(a, b);
    return z;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
