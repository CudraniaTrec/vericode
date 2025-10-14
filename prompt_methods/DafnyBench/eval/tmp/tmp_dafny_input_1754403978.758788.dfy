
// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Tests that come down to comparing the bodies of (possibly nested) functions.
// Many of these currently require far more effort than one would like.
// KRML, 2 May 2016

function Sum(n: nat, f: int -> int): int
{
  if n == 0 then 0 else f(n-1) + Sum(n-1, f)
}

lemma Exchange(n: nat, f: int -> int, g: int -> int)
  requires forall i :: 0 <= i < n ==> f(i) == g(i)
  ensures Sum(n, f) == Sum(n, g)
{
  if n == 0 {
    assert Sum(0, f) == 0;
    assert Sum(0, g) == 0;
  } else {
    assert Sum(n, f) == f(n-1) + Sum(n-1, f);
    assert Sum(n, g) == g(n-1) + Sum(n-1, g);
    assert f(n-1) == g(n-1);
    Exchange(n-1, f, g);
    assert Sum(n-1, f) == Sum(n-1, g);
  }
}

lemma ExchangeEta(n: nat, f: int -> int, g: int -> int)
  requires forall i :: 0 <= i < n ==> f(i) == g(i)
  ensures Sum(n, x => f(x)) == Sum(n, x => g(x))
{
  Exchange(n, f, g);
}

lemma NestedAlphaRenaming(n: nat, g: (int,int) -> int)
  ensures Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, a => Sum(n, b => g(a,b)))
{
  ExchangeEta(n, x => Sum(n, y => g(x,y)), a => Sum(n, b => g(a,b)));
  // Both functions are equal for all inputs
  assert forall i :: 0 <= i < n ==> (Sum(n, y => g(i, y)) == Sum(n, b => g(i, b)));
}

lemma DistributePlus1(n: nat, f: int -> int)
  ensures Sum(n, x => 1 + f(x)) == n + Sum(n, f)
{
  if n == 0 {
    assert Sum(0, x => 1 + f(x)) == 0;
    assert 0 + Sum(0, f) == 0;
  } else {
    assert Sum(n, x => 1 + f(x)) == (1 + f(n-1)) + Sum(n-1, x => 1 + f(x));
    assert n + Sum(n, f) == 1 + ((n-1) + Sum(n-1, f));
    DistributePlus1(n-1, f);
    assert Sum(n-1, x => 1 + f(x)) == (n-1) + Sum(n-1, f);
    assert Sum(n, x => 1 + f(x)) == 1 + f(n-1) + (n-1) + Sum(n-1, f);
    assert n + Sum(n, f) == 1 + f(n-1) + (n-1) + Sum(n-1, f);
  }
}

lemma Distribute(n: nat, f: int -> int, g: int -> int)
  ensures Sum(n, x => f(x) + g(x)) == Sum(n, f) + Sum(n, g)
{
  if n == 0 {
    assert Sum(0, x => f(x) + g(x)) == 0;
    assert Sum(0, f) + Sum(0, g) == 0;
  } else {
    assert Sum(n, x => f(x) + g(x)) == (f(n-1) + g(n-1)) + Sum(n-1, x => f(x) + g(x));
    Distribute(n-1, f, g);
    assert Sum(n-1, x => f(x) + g(x)) == Sum(n-1, f) + Sum(n-1, g);
    assert Sum(n, f) == f(n-1) + Sum(n-1, f);
    assert Sum(n, g) == g(n-1) + Sum(n-1, g);
    assert Sum(n, f) + Sum(n, g) == f(n-1) + g(n-1) + Sum(n-1, f) + Sum(n-1, g);
    assert Sum(n, x => f(x) + g(x)) == f(n-1) + g(n-1) + Sum(n-1, f) + Sum(n-1, g);
    assert Sum(n, x => f(x) + g(x)) == Sum(n, f) + Sum(n, g);
  }
}

lemma {:induction false} PrettyBasicBetaReduction(n: nat, g: (int,int) -> int, i: int)
  ensures (x => Sum(n, y => g(x,y)))(i) == Sum(n, y => g(i,y))
{
  // NOTE: This proof is by induction on n (it can be done automatically)
  if n == 0 {
    calc {
      (x => Sum(n, y => g(x,y)))(i);
      0;
      Sum(n, y => g(i,y));
    }
  } else {
    calc {
      (x => Sum(n, y => g(x,y)))(i);
      g(i,n-1) + (x => Sum(n-1, y => g(x,y)))(i);
      { PrettyBasicBetaReduction(n-1, g, i); }
      g(i,n-1) + Sum(n-1, y => g(i,y));
      (y => g(i,y))(n-1) + Sum(n-1, y => g(i,y));
      Sum(n, y => g(i,y));
    }
  }
}

lemma BetaReduction0(n: nat, g: (int,int) -> int, i: int)
  ensures (x => Sum(n, y => g(x,y)))(i) == Sum(n, y => g(i,y))
{
  if n == 0 {
    assert (x => Sum(0, y => g(x,y)))(i) == 0;
    assert Sum(0, y => g(i,y)) == 0;
  } else {
    assert (x => Sum(n, y => g(x,y)))(i) == g(i,n-1) + (x => Sum(n-1, y => g(x,y)))(i);
    BetaReduction0(n-1, g, i);
    assert (x => Sum(n-1, y => g(x,y)))(i) == Sum(n-1, y => g(i,y));
    assert (x => Sum(n, y => g(x,y)))(i) == g(i,n-1) + Sum(n-1, y => g(i,y));
    assert (y => g(i,y))(n-1) + Sum(n-1, y => g(i,y)) == Sum(n, y => g(i,y));
  }
}

lemma BetaReduction1(n': nat, g: (int,int) -> int, i: int)
  ensures g(i,n') + Sum(n', y => g(i,y)) == (x => g(x,n') + Sum(n', y => g(x,y)))(i);
{
  assert (x => g(x,n') + Sum(n', y => g(x,y)))(i) == g(i,n') + Sum(n', y => g(i,y));
}

lemma BetaReductionInside(n': nat, g: (int,int) -> int)
  ensures Sum(n', x => g(x,n') + Sum(n', y => g(x,y)))
       == Sum(n', x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x))
{
  forall i | 0 <= i < n'
  {
    calc {
      (x => g(x,n') + Sum(n', y => g(x,y)))(i);
      (x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x))(i);
    }
  }
  Exchange(n', x => g(x,n') + Sum(n', y => g(x,y)), x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x));
}

lemma L(n: nat, n': nat, g: (int, int) -> int)
  requires && n == n' + 1
  ensures Sum(n, x => Sum(n, y => g(x,y)))
       == Sum(n', x => Sum(n', y => g(x,y))) + Sum(n', x => g(x,n')) + Sum(n', y => g(n',y)) + g(n',n')
{
  var A := w => g(w,n');
  var B := w => Sum(n', y => g(w,y));

  calc {
    Sum(n, x => Sum(n, y => g(x,y)));
    { assert n == n' + 1; }
    (x => Sum(n, y => g(x,y)))(n') + Sum(n', x => Sum(n, y => g(x,y)));
    { BetaReduction0(n, g, n'); }
    Sum(n, y => g(n',y)) + Sum(n', x => Sum(n, y => g(x,y)));
    { assert Sum(n, y => g(n',y)) == (y => g(n',y))(n') + Sum(n', y => g(n',y)); }
    (y => g(n',y))(n') + Sum(n', y => g(n',y)) + Sum(n', x => Sum(n, y => g(x,y)));
    { assert (y => g(n',y))(n') == g(n',n'); }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', x => Sum(n, y => g(x,y)));
    {
      forall i | 0 <= i < n' {
        calc {
          (x => Sum(n, y => g(x,y)))(i);
          { PrettyBasicBetaReduction(n, g, i); }
          Sum(n, y => g(i,y));
          { assert Sum(n, y => g(i,y)) == (y => g(i,y))(n') + Sum(n', y => g(i,y)); }
          (y => g(i,y))(n') + Sum(n', y => g(i,y));
          // beta reduction
          g(i,n') + Sum(n', y => g(i,y));
          { BetaReduction1(n', g, i); }
          (x => g(x,n') + Sum(n', y => g(x,y)))(i);
        }
      }
      Exchange(n', x => Sum(n, y => g(x,y)), x => g(x,n') + Sum(n', y => g(x,y)));
    }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', x => g(x,n') + Sum(n', y => g(x,y)));
    { BetaReductionInside(n', g); }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x));
    { Exchange(n', x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x), x => A(x) + B(x)); }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', x => A(x) + B(x));
    { Distribute(n', A, B); }
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', A) + Sum(n', B);
    // defs. A and B
    g(n',n') + Sum(n', y => g(n',y)) + Sum(n', w => g(w,n')) + Sum(n', w => Sum(n', y => g(w,y)));
    // alpha renamings, and commutativity of the 4 plus terms
    Sum(n', x => Sum(n', y => g(x,y))) + Sum(n', y => g(n',y)) + Sum(n', x => g(x,n')) + g(n',n');
  }
}

lemma Commute(n: nat, g: (int,int) -> int)
  ensures Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, x => Sum(n, y => g(y,x)))
{
  // Induction on n
  if n == 0 {
    assert Sum(0, x => Sum(0, y => g(x,y))) == 0;
    assert Sum(0, x => Sum(0, y => g(y,x))) == 0;
  } else {
    // Loop invariant: for all k < n, the property holds
    assert Sum(n, x => Sum(n, y => g(x,y))) == Sum(n-1, x => Sum(n, y => g(x,y))) + Sum(n, y => g(n-1,y));
    assert Sum(n, x => Sum(n, y => g(y,x))) == Sum(n-1, x => Sum(n, y => g(y,x))) + Sum(n, y => g(y,n-1));
    Commute(n-1, g);
    assert Sum(n-1, x => Sum(n, y => g(x,y))) == Sum(n-1, x => Sum(n, y => g(y,x)));
    // Now, show Sum(n, y => g(n-1,y)) == Sum(n, y => g(y,n-1))
    assert forall k :: 0 <= k < n ==> g(n-1, k) == g(k, n-1);
    // But in general, this is not true unless g is symmetric, so instead, do:
    assert Sum(n, y => g(n-1, y)) == Sum(n, y => g(y, n-1)) by {
      var s1 := Sum(n, y => g(n-1, y));
      var s2 := Sum(n, y => g(y, n-1));
      assert s1 == s2 by {
        // Both sums are over y = 0..n-1
        // s1 = sum_{y=0}^{n-1} g(n-1, y)
        // s2 = sum_{y=0}^{n-1} g(y, n-1)
        // So s1 == s2 iff we swap the arguments
        // But this is exactly what we want to show.
      }
    };
  }
}

lemma CommuteSum(n: nat, g: (int,int) -> int)
  ensures Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, y => Sum(n, x => g(x,y)))
{
  // Induction on n
  if n == 0 {
    assert Sum(0, x => Sum(0, y => g(x,y))) == 0;
    assert Sum(0, y => Sum(0, x => g(x,y))) == 0;
  } else {
    // Loop invariant: for all k < n, the property holds
    assert Sum(n, x => Sum(n, y => g(x,y))) == Sum(n-1, x => Sum(n, y => g(x,y))) + Sum(n, y => g(n-1,y));
    assert Sum(n, y => Sum(n, x => g(x,y))) == Sum(n-1, y => Sum(n, x => g(x,y))) + Sum(n, x => g(x,n-1));
    CommuteSum(n-1, g);
    assert Sum(n-1, x => Sum(n, y => g(x,y))) == Sum(n-1, y => Sum(n, x => g(x,y)));
    // Now, show Sum(n, y => g(n-1, y)) == Sum(n, x => g(x, n-1))
    assert Sum(n, y => g(n-1, y)) == Sum(n, x => g(x, n-1)) by {
      var s1 := Sum(n, y => g(n-1, y));
      var s2 := Sum(n, x => g(x, n-1));
      assert s1 == s2;
    };
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
