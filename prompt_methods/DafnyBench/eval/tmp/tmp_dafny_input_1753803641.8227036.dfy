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
    // A(x) ==> P(x) || B(x+1)
    if !P(x) {
      // So B(x+1) must hold
      BB(x+1);
    }
  }

  least lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    requires B(x)
  {
    // B(x) ==> Q(x) || A(x+1)
    if !Q(x) {
      // So A(x+1) must hold
      AA(x+1);
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
    BB(x+1);
    // BB(x+1) ensures B(x+1)
    // A(x) <==> B(x+1)
  }

  greatest lemma BB(x: int)  // should be specialized not just for B, but also for A, which is in the same strongly connected component as B in the call graph
    ensures B(x)
  {
    AA(x+1);
    // AA(x+1) ensures A(x+1)
    // B(x) <==> A(x+1)
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
    // A(x) ==> P(x) || A(x+1)
    if !P(x) {
      AA(x+1);
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
