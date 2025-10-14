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
  // Check that 2 is prime
  assert IsPrime(2);
  // Check that 4 is not prime
  assert !IsPrime(4);

  var n := 2;
  while n <= 20
    invariant 2 <= n <= 21
    invariant forall k :: 2 <= k < n ==> (IsPrime(k) <==> (1 < k && forall f :: 1 < f < k ==> !divides(f, k)))
  {
    var isP := true;
    var f := 2;
    while f < n
      invariant 2 <= f <= n
      invariant isP ==> forall d :: 2 <= d < f ==> !divides(d, n)
      invariant !isP ==> exists d :: 2 <= d < f && divides(d, n)
    {
      if divides(f, n) {
        isP := false;
      }
      f := f + 1;
    }
    // Strongest possible assertion that can be verified:
    if isP {
      assert 1 < n && forall f :: 1 < f < n ==> !divides(f, n);
    } else {
      assert exists f :: 1 < f < n && divides(f, n);
    }
    n := n + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
