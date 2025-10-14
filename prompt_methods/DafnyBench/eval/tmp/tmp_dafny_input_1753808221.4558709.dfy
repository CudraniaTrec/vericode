predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  && 1 < i
  && forall f :: 1 < f < i ==> !divides(f, i)
}

method Main()
{
  // Test some assertions about divides and IsPrime
  assert divides(2,4);
  assert !divides(3,4);
  assert IsPrime(2);
  assert IsPrime(3);
  assert !IsPrime(4);

  var n := 2;
  while n <= 10
    invariant 2 <= n <= 11
    invariant forall k :: 2 <= k < n ==> (IsPrime(k) <==> (1 < k && forall f :: 1 < f < k ==> k % f != 0))
  {
    if IsPrime(n) {
      // Strongest assertion we can make: n is prime, so for all f, 1 < f < n ==> n % f != 0
      assert 1 < n;
      assert forall f :: 1 < f < n ==> n % f != 0;
    }
    n := n + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
