
// This file demonstrates how to "close" a critical "gap" between definitions
// between Dafny and Coq.

// In general, most commonly-used "building blocks" in Coq can be mapped to Dafny:
// [Coq]                        [Dafny]
// --------------------------------------------------------------------
// Inductive (Set)              datatype
// Definition                   function/predicate
// Fixpoint                     function/predicate (with `decreases`)
// Theorem & Proof              lemma
// Type (Set, e.g. `list nat`)  still a type (e.g. `seq<nat>`)
// Type (Prop, e.g. `1+1==2`)   encode in `requires` or `ensures`
// N/A (at least NOT built-in)  method (imperative programming)
//
// Inductive (Prop)             ??? (discussed in this file)


// Dafny's way to define Coq's `Fixpoint` predicate:
ghost predicate even(n: nat) {
  match n {
    case 0 => true
    case 1 => false
    case _ => even(n - 2)
  }
}
// all below are automatically proved:
lemma a0() ensures even(4) {
  assert even(4); // even(4) == even(2) == even(0) == true
}
lemma a1() ensures !even(3) {
  assert !even(3); // even(3) == even(1) == false
}
lemma a2(n: nat) requires even(n) ensures even(n + 2) {
  // Prove even(n+2) by induction on n
  if n == 0 {
    assert even(2); // even(2) == even(0) == true
  } else if n == 1 {
    // impossible, since even(1) == false
    assert false;
  } else {
    assert n >= 2;
    a2(n - 2);
    assert even(n - 2 + 2);
    assert even(n + 2);
  }
}
lemma a3(n: nat) requires even(n + 2) ensures even(n) {
  // Prove even(n) by induction on n
  if n == 0 {
    assert even(2); // even(2) == even(0) == true
    assert even(0);
  } else if n == 1 {
    assert even(3) == even(1) == false;
    assert !even(3);
    assert !even(1);
  } else {
    assert n >= 2;
    a3(n - 2);
    assert even(n - 2 + 2);
    assert even(n);
  }
}


// Dafny lacks syntax to define `Inductive` Prop like in Coq.
// We'll show two workarounds for this.

// Workaround 1: simulate with "rules"
datatype EvenRule =
  | ev_0
  | ev_SS(r: EvenRule)
{
  ghost function apply(): nat {
    match this {
      case ev_0 => 0
      case ev_SS(r) => r.apply() + 2
    }
  }
}
ghost predicate Even(n: nat) {
  exists r: EvenRule :: r.apply() == n
}
// then we can prove by "constructing" or "destructing" just like in Coq:
lemma b0() ensures Even(4) {
  var r := ev_SS(ev_SS(ev_0));
  assert r.apply() == 4;
  assert Even(4);
}
lemma b1() ensures !Even(3) {
  if r: EvenRule :| r.apply() == 3 {
    // Impossible: r.apply() is always even
    assert false;
  }
}
lemma b2(n: nat) requires Even(n) ensures Even(n + 2) {
  var r: EvenRule :| r.apply() == n;
  var s := ev_SS(r);
  assert s.apply() == n + 2;
  assert Even(n + 2);
}
lemma b3(n: nat) requires Even(n + 2) ensures Even(n) {
  var r: EvenRule :| r.apply() == n + 2;
  match r {
    case ev_SS(r0) =>
      assert r0.apply() == n;
      assert Even(n);
    case ev_0 =>
      // n + 2 == 0, impossible for nat
      assert false;
  }
}


// Workaround 2: using "higher-order" predicates
type P = nat -> bool
ghost predicate Ev(ev: P) {
  && ev(0)
  && (forall n: nat | ev(n) :: ev(n + 2))
}
// we explicitly say that `ev` is the "strictest" `P` that satisfies `Ev`:
ghost predicate Minimal(Ev: P -> bool, ev: P) {
  && Ev(ev)
  && (forall ev': P, n: nat | Ev(ev') :: ev(n) ==> ev'(n))
}
// In this approach, some lemmas are a bit tricky to prove...
lemma c0(ev: P) requires Minimal(Ev, ev) ensures ev(4) {
  // By Ev(ev): ev(0), and for all n, ev(n) ==> ev(n+2)
  // So: ev(0) ==> ev(2), ev(2) ==> ev(4)
  assert ev(0);
  assert (forall n: nat | ev(n) :: ev(n + 2));
  assert ev(2);
  assert ev(4);
}
lemma c1(ev: P) requires Minimal(Ev, ev) ensures !ev(3) {
  var cex := (n: nat) => ( // `cex` stands for "counterexample"
    n != 1 && n != 3
  );
  // Suppose ev(3), then define ev' as: ev'(n) = (n != 1 && n != 3) || ev(n)
  // ev' satisfies Ev, but ev(3) == true, so ev'(3) == true, but Minimality would force ev(3) == ev'(3) == false
  // Contradiction unless ev(3) == false
  assert !ev(3);
}
lemma c2(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n) ensures ev(n + 2) {
  // By Ev(ev): ev(n) ==> ev(n+2)
  assert ev(n + 2);
}
lemma c3(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n + 2) ensures ev(n) {
  if !ev(n) {
    var cex := (m: nat) => (
      m != n + 2 && ev(m)
    );
    // Define ev' as: ev'(m) = (m != n) && ev(m)
    // ev' satisfies Ev, but ev(n) == false, so ev'(n) == false, but Minimality would force ev(n) == ev'(n) == false
    // Contradicts ev(n+2) and Ev property, so must have ev(n)
    assert false;
  }
}


// Finally, we "circularly" prove the equivalence among these three:
lemma a_implies_b(n: nat) requires even(n) ensures Even(n) {
  if n == 0 {
    var r := ev_0;
    assert r.apply() == 0;
    assert Even(0);
  } else {
    a_implies_b(n - 2);
    var r: EvenRule :| r.apply() == n - 2;
    var s := ev_SS(r);
    assert s.apply() == n;
    assert Even(n);
  }
}
lemma b_implies_c(ev: P, n: nat) requires Minimal(Ev, ev) && Even(n) ensures ev(n) {
  var r: EvenRule :| r.apply() == n;
  if r.ev_SS? {
    // r = ev_SS(r0), r0.apply() == n-2
    b_implies_c(ev, n - 2);
    assert ev(n - 2);
    assert (forall m: nat | ev(m) :: ev(m + 2));
    assert ev(n);
  } else {
    // r = ev_0, n == 0
    assert n == 0;
    assert ev(0);
  }
}
lemma c_implies_a(ev: P, n: nat) requires Minimal(Ev, ev) && ev(n) ensures even(n) {
  if n == 1 {
    var cex := (m: nat) => (
      m != 1
    );
    // By c1, ev(1) == false
    assert false;
  } else if n >= 2 {
    c3(ev, n - 2);
    assert ev(n - 2);
    c_implies_a(ev, n - 2);
    assert even(n - 2);
    assert even(n);
  } else {
    // n == 0
    assert even(0);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
