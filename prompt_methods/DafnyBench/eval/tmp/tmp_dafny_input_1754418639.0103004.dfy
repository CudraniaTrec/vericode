method Ceiling7(n:nat) returns (k:nat)
requires n >= 0
ensures k == n-(n%7)
{
  // n >= 0 by precondition
  // n % 7 is in 0..6
  assert 0 <= n % 7 < 7;
  // n - (n % 7) is a multiple of 7
  assert ((n - (n % 7)) % 7) == 0;
  // n - (n % 7) <= n
  assert n - (n % 7) <= n;
  k := n-(n%7);
  assert k == n-(n%7);
}

method test7() {
  var k: nat;
  k := Ceiling7(43);
  assert k == 42;
  k := Ceiling7(6);
  assert k == 0;
  k := Ceiling7(1000);
  assert k == 994;
  k := Ceiling7(7);
  assert k == 7;
  k := Ceiling7(70);
  assert k == 70;
}
function abs(a: real) : real {if a>0.0 then a else -a}
