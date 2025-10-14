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
    // nothing to prove
  } else {
    assert f(n-1) == g(n-1);
    Exchange(n-1, f, g);
    assert Sum(n-1, f) == Sum(n-1, g);
    assert Sum(n, f) == f(n-1) + Sum(n-1, f);
    assert Sum(n, g) == g(n-1) + Sum(n-1, g);
    assert Sum(n, f) == Sum(n, g);
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
  // alpha renaming
  Exchange(n, x => Sum(n, y => g(x,y)), a => Sum(n, b => g(a,b)));
}

lemma DistributePlus1(n: nat, f: int -> int)
  ensures Sum(n, x => 1 + f(x)) == n + Sum(n, f)
{
  if n == 0 {
    // nothing to prove
  } else {
    DistributePlus1(n-1, f);
    assert Sum(n, x => 1 + f(x)) == (1 + f(n-1)) + Sum(n-1, x => 1 + f(x));
    assert Sum(n-1, x => 1 + f(x)) == (n-1) + Sum(n-1, f);
    assert Sum(n, x => 1 + f(x)) == (1 + f(n-1)) + (n-1 + Sum(n-1, f));
    assert Sum(n, x => 1 + f(x)) == n + f(n-1) + Sum(n-1, f);
    assert Sum(n, x => 1 + f(x)) == n + Sum(n, f);
  }
}

lemma Distribute(n: nat, f: int -> int, g: int -> int)
  ensures Sum(n, x => f(x) + g(x)) == Sum(n, f) + Sum(n, g)
{
  if n == 0 {
    // nothing to prove
  } else {
    Distribute(n-1, f, g);
    assert Sum(n, x => f(x) + g(x)) == (f(n-1) + g(n-1)) + Sum(n-1, x => f(x) + g(x));
    assert Sum(n-1, x => f(x) + g(x)) == Sum(n-1, f) + Sum(n-1, g);
    assert Sum(n, x => f(x) + g(x)) == (f(n-1) + g(n-1)) + (Sum(n-1, f) + Sum(n-1, g));
    assert Sum(n, x => f(x) + g(x)) == (f(n-1) + Sum(n-1, f)) + (g(n-1) + Sum(n-1, g));
    assert Sum(n, x => f(x) + g(x)) == Sum(n, f) + Sum(n, g);
  }
}

lemma {:induction false} PrettyBasicBetaReduction(n: nat, g: (int,int) -> int, i: int)
  ensures (x => Sum(n, y => g(x,y)))(i) == Sum(n, y => g(i,y))
{
  if n == 0 {
    // nothing to prove
  } else {
    PrettyBasicBetaReduction(n-1, g, i);
    assert (x => Sum(n, y => g(x,y)))(i) == g(i, n-1) + (x => Sum(n-1, y => g(x,y)))(i);
    assert (x => Sum(n-1, y => g(x,y)))(i) == Sum(n-1, y => g(i, y));
    assert (x => Sum(n, y => g(x,y)))(i) == g(i, n-1) + Sum(n-1, y => g(i, y));
    assert (y => g(i, y))(n-1) + Sum(n-1, y => g(i, y)) == Sum(n, y => g(i, y));
    assert (x => Sum(n, y => g(x,y)))(i) == Sum(n, y => g(i, y));
  }
}

lemma BetaReduction0(n: nat, g: (int,int) -> int, i: int)
  ensures (x => Sum(n, y => g(x,y)))(i) == Sum(n, y => g(i,y))
{
  PrettyBasicBetaReduction(n, g, i);
}

lemma BetaReduction1(n': nat, g: (int,int) -> int, i: int)
  ensures g(i,n') + Sum(n', y => g(i,y)) == (x => g(x,n') + Sum(n', y => g(x,y)))(i);
{
  // direct by definition
}

lemma BetaReductionInside(n': nat, g: (int,int) -> int)
  ensures Sum(n', x => g(x,n') + Sum(n', y => g(x,y)))
       == Sum(n', x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x))
{
  Exchange(n', x => g(x,n') + Sum(n', y => g(x,y)), x => (w => g(w,n'))(x) + (w => Sum(n', y => g(w,y)))(x));
}

lemma L(n: nat, n': nat, g: (int, int) -> int)
  requires && n == n' + 1
  ensures Sum(n, x => Sum(n, y => g(x,y)))
       == Sum(n', x => Sum(n', y => g(x,y))) + Sum(n', x => g(x,n')) + Sum(n', y => g(n',y)) + g(n',n')
{
  var A := w => g(w,n');
  var B := w => Sum(n', y => g(w,y));

  // Step 1: Expand Sum(n, x => Sum(n, y => g(x,y)))
  // We proceed by induction on n, and use the definition of Sum
  // Loop invariant: for all k <= n, the expansion holds for k and k-1
  // (not an actual loop, but for clarity)
  calc {
    Sum(n, x => Sum(n, y => g(x,y)));
    // By definition of Sum
    Sum(n-1, x => Sum(n, y => g(x,y))) + (x => Sum(n, y => g(x,y)))(n-1);
    { assert n == n' + 1; }
    Sum(n', x => Sum(n, y => g(x,y))) + (x => Sum(n, y => g(x,y)))(n');
    // Beta reduction
    { BetaReduction0(n, g, n'); }
    Sum(n', x => Sum(n, y => g(x,y))) + Sum(n, y => g(n', y));
    // Expand Sum(n, y => g(n', y))
    Sum(n', x => Sum(n, y => g(x,y))) + Sum(n-1, y => g(n', y)) + (y => g(n', y))(n-1);
    { assert (y => g(n', y))(n-1) == g(n', n-1); }
    Sum(n', x => Sum(n, y => g(x,y))) + Sum(n', y => g(n', y)) + g(n', n-1);
    // Now expand Sum(n', x => Sum(n, y => g(x,y)))
    // For each x < n', Sum(n, y => g(x,y)) = Sum(n', y => g(x,y)) + g(x, n-1)
    // Prove by induction on x
    {
      forall i | 0 <= i < n' {
        calc {
          (x => Sum(n, y => g(x,y)))(i);
          // By definition of Sum
          Sum(n-1, y => g(i, y)) + (y => g(i, y))(n-1);
          Sum(n', y => g(i, y)) + g(i, n-1);
        }
      }
    }
    // So Sum(n', x => Sum(n, y => g(x,y))) = Sum(n', x => Sum(n', y => g(x,y)) + g(x, n-1))
    // Distribute sum
    { Distribute(n', x => Sum(n', y => g(x,y)), x => g(x, n-1)); }
    Sum(n', x => Sum(n', y => g(x,y))) + Sum(n', x => g(x, n-1)) + Sum(n', y => g(n', y)) + g(n', n-1);
    // Rearranging terms
    Sum(n', x => Sum(n', y => g(x,y))) + Sum(n', y => g(n', y)) + Sum(n', x => g(x, n-1)) + g(n', n-1);
  }
}

lemma Commute(n: nat, g: (int,int) -> int)
  ensures Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, x => Sum(n, y => g(y,x)))
{
  // Strongest annotation: double sum over (i,j) is equal to sum over (j,i)
  // So, Sum(n, x => Sum(n, y => g(x,y))) = Sum(n, x => Sum(n, y => g(y,x)))
  // This can be proved by observing that both sum over all pairs (i,j) in [0,n)^2
  // and swapping the order of summation does not change the value.
  // We proceed by induction on n.
  if n == 0 {
    // nothing to prove
  } else {
    Commute(n-1, g);
    assert Sum(n, x => Sum(n, y => g(x,y))) == Sum(n-1, x => Sum(n, y => g(x,y))) + Sum(n, y => g(n-1, y));
    assert Sum(n, x => Sum(n, y => g(y,x))) == Sum(n-1, x => Sum(n, y => g(y,x))) + Sum(n, y => g(y, n-1));
    assert Sum(n-1, x => Sum(n, y => g(x,y))) == Sum(n-1, x => Sum(n, y => g(y,x)));
    // Now, Sum(n, y => g(n-1, y)) == Sum(n, y => g(y, n-1)) by swapping y <-> x
    // Prove by induction on n
    // We can use Exchange to show this
    Exchange(n, y => g(n-1, y), y => g(y, n-1));
    assert Sum(n, y => g(n-1, y)) == Sum(n, y => g(y, n-1));
    assert Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, x => Sum(n, y => g(y,x)));
  }
}

lemma CommuteSum(n: nat, g: (int,int) -> int)
  ensures Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, y => Sum(n, x => g(x,y)))
{
  // The order of summation can be swapped.
  // This is a property of finite sums and follows from the definition.
  // We proceed by induction on n.
  if n == 0 {
    // nothing to prove
  } else {
    CommuteSum(n-1, g);
    assert Sum(n, x => Sum(n, y => g(x,y))) == Sum(n-1, x => Sum(n, y => g(x,y))) + Sum(n, y => g(n-1, y));
    assert Sum(n, y => Sum(n, x => g(x,y))) == Sum(n-1, y => Sum(n, x => g(x,y))) + Sum(n, x => g(x, n-1));
    assert Sum(n-1, x => Sum(n, y => g(x,y))) == Sum(n-1, y => Sum(n, x => g(x,y)));
    // Now, Sum(n, y => g(n-1, y)) == Sum(n, x => g(x, n-1)) by swapping x <-> y
    Exchange(n, y => g(n-1, y), x => g(x, n-1));
    assert Sum(n, y => g(n-1, y)) == Sum(n, x => g(x, n-1));
    assert Sum(n, x => Sum(n, y => g(x,y))) == Sum(n, y => Sum(n, x => g(x,y)));
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
