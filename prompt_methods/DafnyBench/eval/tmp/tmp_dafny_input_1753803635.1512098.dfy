
// RUN: %dafny /compile:0 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module InductiveThings {
  ghost predicate P(x: int)
  ghost predicate Q(x: int)

  least predicate A(x: int)
  {
    P(x) || B(x+1)
  }

  least predicate B(x: int)
  {
    Q(x) || A(x+1)
  }

  least lemma AA(x: int)  // should be specialized not just for A, but also for B, which is in the same strongly connected component as A in the call graph
    requires A(x)
  {
    // Strongest possible annotation: if A(x), then either P(x) or B(x+1)
    if P(x) {
      // nothing to do
      assert A(x); // A(x) holds by precondition
      assert P(x); // by branch
    } else {
      assert B(x+1); // by definition of A(x)
      if B(x+1) {  // this one should be replaced by B#[_k-1](x+1)
        BB(x+1);
      }
    }
  }

  least lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    requires B(x)
  {
    // Strongest possible annotation: if B(x), then either Q(x) or A(x+1)
    if Q(x) {
      // nothing to do
      assert B(x); // B(x) holds by precondition
      assert Q(x); // by branch
    } else {
      assert A(x+1); // by definition of B(x)
      if A(x+1) {  // this one should be replaced by A#[_k-1](x+1)
        AA(x+1);
      }
    }
  }
}

module CoThings {
  greatest predicate A(x: int)
  {
    B(x+1)
  }

  greatest predicate B(x: int)
  {
    A(x+1)
  }

  greatest lemma AA(x: int)  // should be specialized not just for A, but also for B, which is in the same strongly connected component as A in the call graph
    ensures A(x)
  {
    // Strongest possible annotation: must show A(x) holds
    BB(x+1);
    assert B(x+1); // by BB's postcondition
    assert A(x);   // by definition of A(x)
  }

  greatest lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    ensures B(x)
  {
    // Strongest possible annotation: must show B(x) holds
    AA(x+1);
    assert A(x+1); // by AA's postcondition
    assert B(x);   // by definition of B(x)
  }
}

module SingleThings {
  ghost predicate P(x: int)

  least predicate A(x: int)
  {
    P(x) || A(x+1)
  }

  least lemma AA(x: int)  // should be specialized just for A
    requires A(x)
  {
    // Strongest possible annotation: if A(x), then either P(x) or A(x+1)
    if P(x) {
      assert A(x); // by precondition
      assert P(x); // by branch
    } else {
      assert A(x+1); // by definition of A(x)
      if A(x+1) {  // this one should be replaced by B#[_k-1](x+1)
        AA(x+1);
      }
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
