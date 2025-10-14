
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A definition of a co-inductive datatype Stream, whose values are possibly
// infinite lists.
codatatype Stream<T> = SNil | SCons(head: T, tail: Stream<T>)

/*
  A function that returns a stream consisting of all integers upwards of n.
  The self-call sits in a productive position and is therefore not subject to
  termination checks.  The Dafny compiler turns this co-recursive call into a
  lazily evaluated call, evaluated at the time during the program execution
  when the SCons is destructed (if ever).
*/

function Up(n: int): Stream<int>
{
  SCons(n, Up(n+1))
}

/*
  A function that returns a stream consisting of all multiples
  of 5 upwards of n.  Note that the first self-call sits in a
  productive position and is thus co-recursive.  The second self-call
  is not in a productive position and therefore it is subject to
  termination checking; in particular, each recursive call must
  decrease the specific variant function.
 */

function FivesUp(n: int): Stream<int>
{
  if n % 5 == 0 then SCons(n, FivesUp(n+1))
  else FivesUp(n+1)
}

// A co-predicate that holds for those integer streams where every value is greater than 0.
copredicate Pos(s: Stream<int>)
{
  match s
  case SNil => true
  case SCons(x, rest) => x > 0 && Pos(rest)
}

// SAppend looks almost exactly like Append, but cannot have 'decreases'
// clause, as it is possible it will never terminate.
function SAppend(xs: Stream, ys: Stream): Stream
{
  match xs
  case SNil => ys
  case SCons(x, rest) => SCons(x, SAppend(rest, ys))
}

/*
  Example: associativity of append on streams.

  The first method proves that append is associative when we consider first
  \S{k} elements of the resulting streams.  Equality is treated as any other
  recursive co-predicate, and has it k-th unfolding denoted as ==#[k].

  The second method invokes the first one for all ks, which lets us prove the
  postcondition (by (F_=)).  Interestingly, in the SNil case in the first
  method, we actually prove ==, but by (F_=) applied in the opposite direction
  we also get ==#[k].
*/

lemma {:induction false} SAppendIsAssociativeK(k:nat, a:Stream, b:Stream, c:Stream)
  ensures SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c));
{
  // Strongest invariant: For all k, SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c))
  match (a) {
  case SNil =>
    // assert SAppend(SAppend(SNil, b), c) == SAppend(SNil, SAppend(b, c));
    // SAppend(SNil, b) == b, so SAppend(b, c) == SAppend(SNil, SAppend(b, c))
    // So SAppend(SAppend(SNil, b), c) == SAppend(b, c)
    // SAppend(SNil, SAppend(b, c)) == SAppend(b, c)
    // So both sides are equal
    assert SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
  case SCons(h, t) =>
    if (k > 0) {
      // Inductive step: need to show for k, assuming for k-1
      // SAppend(SAppend(SCons(h, t), b), c) ==#[k] SAppend(SCons(h, t), SAppend(b, c))
      // SAppend(SCons(h, t), b) == SCons(h, SAppend(t, b))
      // SAppend(SCons(h, SAppend(t, b)), c) == SCons(h, SAppend(SAppend(t, b), c))
      // SAppend(SCons(h, t), SAppend(b, c)) == SCons(h, SAppend(t, SAppend(b, c)))
      // So need SAppend(SAppend(t, b), c) ==#[k-1] SAppend(t, SAppend(b, c))
      SAppendIsAssociativeK(k - 1, t, b, c);
      // assert SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c));
    }
  }
}

lemma SAppendIsAssociative(a:Stream, b:Stream, c:Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
{
  // Strongest annotation: for all k, SAppendIsAssociativeK(k, a, b, c) holds
  forall k:nat 
    ensures SAppend(SAppend(a, b), c) ==#[k] SAppend(a, SAppend(b, c))
  {
    SAppendIsAssociativeK(k, a, b, c);
  }
  // assert for clarity only, postcondition follows directly from it
  assert SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
}

// Equivalent proof using the colemma syntax.
colemma {:induction false} SAppendIsAssociativeC(a:Stream, b:Stream, c:Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
{
  // Strongest annotation: for all a, b, c, SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c))
  match (a) {
  case SNil =>
    assert SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
  case SCons(h, t) =>
    SAppendIsAssociativeC(t, b, c);
    // assert SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
  }
}

// In fact the proof can be fully automatic.
colemma SAppendIsAssociative_Auto(a:Stream, b:Stream, c:Stream)
  ensures SAppend(SAppend(a, b), c) == SAppend(a, SAppend(b, c));
{
  // No code needed; proof is automatic.
}

// Prove that Up(n) is positive for n > 0
colemma {:induction false} UpPos(n:int)
  requires n > 0;
  ensures Pos(Up(n));
{
  // Strongest annotation: Pos(Up(n)) holds for all n > 0
  // Up(n) = SCons(n, Up(n+1))
  // So Pos(Up(n)) = n > 0 && Pos(Up(n+1))
  // n > 0 holds by precondition, so need Pos(Up(n+1))
  UpPos(n+1);
  // assert Pos(Up(n));
}

colemma UpPos_Auto(n:int)
  requires n > 0;
  ensures Pos(Up(n));
{
  // Proof is automatic.
}

// This does induction and coinduction in the same proof.
colemma {:induction false} FivesUpPos(n:int)
  requires n > 0;
  ensures Pos(FivesUp(n));
{
  // Strongest annotation: Pos(FivesUp(n)) holds for all n > 0
  if (n % 5 == 0) {
    // FivesUp(n) = SCons(n, FivesUp(n+1))
    // So Pos(FivesUp(n)) = n > 0 && Pos(FivesUp(n+1))
    // n > 0 holds by precondition, so need Pos(FivesUp(n+1))
    FivesUpPos#[_k - 1](n + 1);
    // assert Pos(FivesUp(n));
  } else {
    // FivesUp(n) = FivesUp(n+1)
    FivesUpPos#[_k](n + 1);
    // assert Pos(FivesUp(n));
  }
}

// Again, Dafny can just employ induction tactic and do it automatically.
// The only hint required is the decrease clause.
colemma FivesUpPos_Auto(n:int)
  requires n > 0;
  ensures Pos(FivesUp(n));
{
  // Proof is automatic.
}

function abs(a: real) : real {if a>0.0 then a else -a}
