
predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  && 1<i
  && ( forall f :: 1 < f < i ==> !divides(f, i) )
}

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
{
  var f := 2;
  while (f < i)
    invariant 2 <= f <= i
    invariant forall k :: 2 <= k < f ==> !divides(k, i)
  {
    if i % f == 0 {
      assert divides(f, i); // triggers the existential for !IsPrime
      return false;
    }
    f := f + 1;
  }
  return true;
}

method Main()
{
  var a := test_prime(3);
  var b := test_prime(4);
  var c := test_prime(5);
}

function abs(a: real) : real {if a>0.0 then a else -a}
