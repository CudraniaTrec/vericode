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

  // Strongest possible loop invariants for checking primes up to 10
  var n := 2;
  while n <= 10
    invariant 2 <= n <= 11
    invariant forall k :: 2 <= k < n ==> (IsPrime(k) <==> (1 < k && forall f :: 1 < f < k ==> k % f != 0))
  {
    if IsPrime(n) {
      assert forall f :: 1 < f < n ==> n % f != 0;
    } else {
      assert exists f :: 1 < f < n && n % f == 0;
    }
    n := n + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
