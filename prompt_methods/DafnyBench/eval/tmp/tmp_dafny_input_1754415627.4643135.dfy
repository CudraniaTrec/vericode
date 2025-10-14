// RUN: %testDafnyForEachResolver "%s"


// Here is a function "f" and three axioms (that is, unproved lemmas) about "f":

ghost function f(x: int, y: int): int

lemma Associativity(x: int, y: int, z: int)
  ensures f(x, f(y, z)) == f(f(x, y), z)

lemma Monotonicity(y: int, z: int)
  requires y <= z
  ensures forall x :: f(x, y) <= f(x, z)

lemma DiagonalIdentity(x: int)
  ensures f(x, x) == x

// From these axioms, we can prove a lemma about "f":

method CalculationalStyleProof(a: int, b: int, c: int, x: int)
  requires c <= x == f(a, b)
  ensures f(a, f(b, c)) <= x
{
  calc {
    f(a, f(b, c));
  ==  { Associativity(a, b, c); }
    f(f(a, b), c);
  ==  { assert f(a, b) == x; }
    f(x, c);
  <=  { assert c <= x; Monotonicity(c, x); }
    f(x, x);
  ==  { DiagonalIdentity(x); }
    x;
  }
}

// Here's the same lemma, but with a proof written in a different style.
// (An explanation of the constructs in this lemma is found below.)

method DifferentStyleProof(a: int, b: int, c: int, x: int)
  requires A: c <= x
  requires B: x == f(a, b)
  ensures f(a, f(b, c)) <= x
{
  // Step 0: f(a, f(b, c)) == f(f(a, b), c)    by associativity
  assert 0: f(a, f(b, c)) == f(f(a, b), c) by {
    Associativity(a, b, c);
  }

  // Step 1: f(f(a, b), c) == f(x, c)         by x == f(a, b)
  assert 1: f(f(a, b), c) == f(x, c) by {
    reveal B;
  }

  // Step 2: c <= x (from requires A)
  assert 2: c <= x by {
    reveal A;
  }

  // Step 3: f(x, c) <= f(x, x)               by monotonicity, c <= x
  assert 3: f(x, c) <= f(x, x) by {
    Monotonicity(c, x);
  }

  // Step 4: f(x, x) == x                     by diagonal identity
  assert 4: f(x, x) == x by {
    DiagonalIdentity(x);
  }

  // Step 5: f(a, f(b, c)) <= x
  assert 5: f(a, f(b, c)) <= x by {
    reveal 0, 1;
    reveal 2;
    reveal 3, 4;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
