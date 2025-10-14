
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
    // Strongest annotation: show that A(x) holds by induction on the least predicate
    if B(x+1) {  // this one should be replaced by B#[_k-1](x+1)
      assert B(x+1); // By definition of A(x)
      BB(x+1);
    } else {
      assert P(x); // By definition of A(x)
    }
  }

  least lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    requires B(x)
  {
    // Strongest annotation: show that B(x) holds by induction on the least predicate
    if A(x+1) {  // this one should be replaced by A#[_k-1](x+1)
      assert A(x+1); // By definition of B(x)
      AA(x+1);
    } else {
      assert Q(x); // By definition of B(x)
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
    // Strongest annotation: show that A(x) holds by coinduction
    BB(x+1);
    assert B(x+1); // By postcondition of BB
    // By definition of A(x), A(x) holds
  }

  greatest lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    ensures B(x)
  {
    // Strongest annotation: show that B(x) holds by coinduction
    AA(x+1);
    assert A(x+1); // By postcondition of AA
    // By definition of B(x), B(x) holds
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
    // Strongest annotation: show that A(x) holds by induction on the least predicate
    if A(x+1) {  // this one should be replaced by B#[_k-1](x+1)
      assert A(x+1); // By definition of A(x)
      AA(x+1);
    } else {
      assert P(x); // By definition of A(x)
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
