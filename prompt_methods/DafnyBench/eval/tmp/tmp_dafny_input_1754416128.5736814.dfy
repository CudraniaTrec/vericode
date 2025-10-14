
// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// ----- Stream

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

ghost function append(M: Stream, N: Stream): Stream
  decreases M
{
  match M
  case Nil => N
  case Cons(t, M') => Cons(t, append(M', N))
}

// ----- f, g, and maps

type X

ghost function f(x: X): X
ghost function g(x: X): X

ghost function map_f(M: Stream<X>): Stream<X>
  decreases M
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(f(x), map_f(N))
}

ghost function map_g(M: Stream<X>): Stream<X>
  decreases M
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(g(x), map_g(N))
}

ghost function map_fg(M: Stream<X>): Stream<X>
  decreases M
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(f(g(x)), map_fg(N))
}

// ----- Theorems

// map (f * g) M = map f (map g M)
greatest lemma Theorem0(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  match (M) {
    case Nil =>
    case Cons(x, N) =>
      assert map_fg(N) == map_f(map_g(N));
      Theorem0(N);
      assert map_fg(M) == Cons(f(g(x)), map_fg(N));
      assert map_f(map_g(M)) == Cons(f(g(x)), map_f(map_g(N)));
      assert map_fg(M) == map_f(map_g(M));
  }
}
greatest lemma Theorem0_Alt(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  if (M.Cons?) {
    assert map_fg(M.tail) == map_f(map_g(M.tail));
    Theorem0_Alt(M.tail);
    assert map_fg(M) == Cons(f(g(M.head)), map_fg(M.tail));
    assert map_f(map_g(M)) == Cons(f(g(M.head)), map_f(map_g(M.tail)));
    assert map_fg(M) == map_f(map_g(M));
  }
}
lemma Theorem0_Par(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  forall k: nat
    ensures map_fg(M) ==#[k] map_f(map_g(M));
  {
    Theorem0_Ind(k, M);
  }
}
lemma Theorem0_Ind(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M));
{
  if (k != 0) {
    match (M) {
      case Nil =>
        assert map_fg(M) == Nil;
        assert map_f(map_g(M)) == Nil;
        assert map_fg(M) ==#[k] map_f(map_g(M));
      case Cons(x, N) =>
        assert map_fg(N) ==#[k-1] map_f(map_g(N));
        Theorem0_Ind(k-1, N);
        assert map_fg(M) == Cons(f(g(x)), map_fg(N));
        assert map_f(map_g(M)) == Cons(f(g(x)), map_f(map_g(N)));
        assert map_fg(M) ==#[k] map_f(map_g(M));
    }
  }
}
lemma Theorem0_AutoInd(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M));
{
  // strongest annotation: induction on k and M
  if k == 0 {
    // nothing to prove
  } else if M.Cons? {
    assert map_fg(M.tail) ==#[k-1] map_f(map_g(M.tail));
    Theorem0_AutoInd(k-1, M.tail);
    assert map_fg(M) == Cons(f(g(M.head)), map_fg(M.tail));
    assert map_f(map_g(M)) == Cons(f(g(M.head)), map_f(map_g(M.tail)));
    assert map_fg(M) ==#[k] map_f(map_g(M));
  } else {
    assert map_fg(M) == Nil;
    assert map_f(map_g(M)) == Nil;
    assert map_fg(M) ==#[k] map_f(map_g(M));
  }
}

// map f (append M N) = append (map f M) (map f N)
greatest lemma Theorem1(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  match (M) {
    case Nil =>
      assert append(M, N) == N;
      assert map_f(append(M, N)) == map_f(N);
      assert map_f(M) == Nil;
      assert append(map_f(M), map_f(N)) == map_f(N);
      assert map_f(append(M, N)) == append(map_f(M), map_f(N));
    case Cons(x, M') =>
      assert map_f(append(M', N)) == append(map_f(M'), map_f(N));
      Theorem1(M', N);
      assert append(M, N) == Cons(x, append(M'.TailType(), N));
      assert map_f(append(M, N)) == Cons(f(x), map_f(append(M', N)));
      assert map_f(M) == Cons(f(x), map_f(M'));
      assert append(map_f(M), map_f(N)) == Cons(f(x), append(map_f(M'), map_f(N)));
      assert map_f(append(M, N)) == append(map_f(M), map_f(N));
  }
}
greatest lemma Theorem1_Alt(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  if (M.Cons?) {
    assert map_f(append(M.tail, N)) == append(map_f(M.tail), map_f(N));
    Theorem1_Alt(M.tail, N);
    assert map_f(append(M, N)) == Cons(f(M.head), map_f(append(M.tail, N)));
    assert map_f(M) == Cons(f(M.head), map_f(M.tail));
    assert append(map_f(M), map_f(N)) == Cons(f(M.head), append(map_f(M.tail), map_f(N)));
    assert map_f(append(M, N)) == append(map_f(M), map_f(N));
  } else {
    assert append(M, N) == N;
    assert map_f(append(M, N)) == map_f(N);
    assert map_f(M) == Nil;
    assert append(map_f(M), map_f(N)) == map_f(N);
    assert map_f(append(M, N)) == append(map_f(M), map_f(N));
  }
}
lemma Theorem1_Par(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  forall k: nat
    ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
  {
    Theorem1_Ind(k, M, N);
  }
}
lemma Theorem1_Ind(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
{
  // this time, try doing the 'if' inside the 'match' (instead of the other way around)
  match (M) {
    case Nil =>
      assert append(M, N) == N;
      assert map_f(append(M, N)) == map_f(N);
      assert map_f(M) == Nil;
      assert append(map_f(M), map_f(N)) == map_f(N);
      assert map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
    case Cons(x, M') =>
      if (k != 0) {
        assert map_f(append(M', N)) ==#[k-1] append(map_f(M'), map_f(N));
        Theorem1_Ind(k-1, M', N);
        assert map_f(append(M, N)) == Cons(f(x), map_f(append(M', N)));
        assert map_f(M) == Cons(f(x), map_f(M'));
        assert append(map_f(M), map_f(N)) == Cons(f(x), append(map_f(M'), map_f(N)));
        assert map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
      } else {
        // nothing to prove
      }
  }
}
lemma Theorem1_AutoInd(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
{
  if k == 0 {
    // nothing to prove
  } else if M.Cons? {
    assert map_f(append(M.tail, N)) ==#[k-1] append(map_f(M.tail), map_f(N));
    Theorem1_AutoInd(k-1, M.tail, N);
    assert map_f(append(M, N)) == Cons(f(M.head), map_f(append(M.tail, N)));
    assert map_f(M) == Cons(f(M.head), map_f(M.tail));
    assert append(map_f(M), map_f(N)) == Cons(f(M.head), append(map_f(M.tail), map_f(N)));
    assert map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
  } else {
    assert append(M, N) == N;
    assert map_f(append(M, N)) == map_f(N);
    assert map_f(M) == Nil;
    assert append(map_f(M), map_f(N)) == map_f(N);
    assert map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
  }
}
lemma Theorem1_AutoForall()
{
  // assert forall k: nat, M, N :: map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));  // TODO: this is not working yet, apparently
}

// append NIL M = M
lemma Theorem2(M: Stream<X>)
  ensures append(Nil, M) == M;
{
  // trivial
  assert append(Nil, M) == M;
}

// append M NIL = M
greatest lemma Theorem3(M: Stream<X>)
  ensures append(M, Nil) == M;
{
  match (M) {
    case Nil =>
      assert append(M, Nil) == Nil;
      assert M == Nil;
      assert append(M, Nil) == M;
    case Cons(x, N) =>
      assert append(N, Nil) == N;
      Theorem3(N);
      assert append(M, Nil) == Cons(x, append(N, Nil));
      assert M == Cons(x, N);
      assert append(M, Nil) == M;
  }
}
greatest lemma Theorem3_Alt(M: Stream<X>)
  ensures append(M, Nil) == M;
{
  if (M.Cons?) {
    assert append(M.tail, Nil) == M.tail;
    Theorem3_Alt(M.tail);
    assert append(M, Nil) == Cons(M.head, append(M.tail, Nil));
    assert M == Cons(M.head, M.tail);
    assert append(M, Nil) == M;
  } else {
    assert append(M, Nil) == Nil;
    assert M == Nil;
    assert append(M, Nil) == M;
  }
}

// append M (append N P) = append (append M N) P
greatest lemma Theorem4(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{
  match (M) {
    case Nil =>
      assert append(M, append(N, P)) == append(N, P);
      assert append(append(M, N), P) == append(N, P);
      assert append(M, append(N, P)) == append(append(M, N), P);
    case Cons(x, M') =>
      assert append(M', append(N, P)) == append(append(M', N), P);
      Theorem4(M', N, P);
      assert append(M, append(N, P)) == Cons(x, append(M', append(N, P)));
      assert append(append(M, N), P) == Cons(x, append(append(M', N), P));
      assert append(M, append(N, P)) == append(append(M, N), P);
  }
}
greatest lemma Theorem4_Alt(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{
  if (M.Cons?) {
    assert append(M.tail, append(N, P)) == append(append(M.tail, N), P);
    Theorem4_Alt(M.tail, N, P);
    assert append(M, append(N, P)) == Cons(M.head, append(M.tail, append(N, P)));
    assert append(append(M, N), P) == Cons(M.head, append(append(M.tail, N), P));
    assert append(M, append(N, P)) == append(append(M, N), P);
  } else {
    assert append(M, append(N, P)) == append(N, P);
    assert append(append(M, N), P) == append(N, P);
    assert append(M, append(N, P)) == append(append(M, N), P);
  }
}

// ----- Flatten

// Flatten can't be written as just:
//
//     function SimpleFlatten(M: Stream<Stream>): Stream
//     {
//       match M
//       case Nil => Nil
//       case Cons(s, N) => append(s, SimpleFlatten(N))
//     }
//
// because this function fails to be productive given an infinite stream of Nil's.
// Instead, here are two variations of SimpleFlatten.  The first variation (FlattenStartMarker)
// prepends a "startMarker" to each of the streams in "M".  The other (FlattenNonEmpties)
// insists that "M" contain no empty streams.  One can prove a theorem that relates these
// two versions.

// This first variation of Flatten returns a stream of the streams in M, each preceded with
// "startMarker".

ghost function FlattenStartMarker<T>(M: Stream<Stream>, startMarker: T): Stream
  decreases M
{
  PrependThenFlattenStartMarker(Nil, M, startMarker)
}

ghost function PrependThenFlattenStartMarker<T>(prefix: Stream, M: Stream<Stream>, startMarker: T): Stream
  decreases prefix, M
{
  match prefix
  case Cons(hd, tl) =>
    Cons(hd, PrependThenFlattenStartMarker(tl, M, startMarker))
  case Nil =>
    match M
    case Nil => Nil
    case Cons(s, N) => Cons(startMarker, PrependThenFlattenStartMarker(s, N, startMarker))
}

// The next variation of Flatten requires M to contain no empty streams.

greatest predicate StreamOfNonEmpties(M: Stream<Stream>)
{
  match M
  case Nil => true
  case Cons(s, N) => s.Cons? && StreamOfNonEmpties(N)
}

ghost function FlattenNonEmpties(M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
  decreases M
{
  PrependThenFlattenNonEmpties(Nil, M)
}

ghost function PrependThenFlattenNonEmpties(prefix: Stream, M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
  decreases prefix, M
{
  match prefix
  case Cons(hd, tl) =>
    Cons(hd, PrependThenFlattenNonEmpties(tl, M))
  case Nil =>
    match M
    case Nil => Nil
    case Cons(s, N) => Cons(s.head, PrependThenFlattenNonEmpties(s.tail, N))
}

// We can prove a theorem that links the previous two variations of flatten.  To
// do that, we first define a function that prepends an element to each stream
// of a given stream of streams.

ghost function Prepend<T>(x: T, M: Stream<Stream>): Stream<Stream>
  decreases M
{
  match M
  case Nil => Nil
  case Cons(s, N) => Cons(Cons(x, s), Prepend(x, N))
}

greatest lemma Prepend_Lemma<T>(x: T, M: Stream<Stream>)
  ensures StreamOfNonEmpties(Prepend(x, M));
{
  match M {
    case Nil =>
      assert Prepend(x, M) == Nil;
      assert StreamOfNonEmpties(Prepend(x, M));
    case Cons(s, N) =>
      assert Prepend(x, N).Cons? || Prepend(x, N) == Nil;
      Prepend_Lemma(x, N);
      assert Prepend(x, M) == Cons(Cons(x, s), Prepend(x, N));
      assert Cons(x, s).Cons?;
      assert StreamOfNonEmpties(Prepend(x, N));
      assert StreamOfNonEmpties(Prepend(x, M));
  }
}

lemma Theorem_Flatten<T>(M: Stream<Stream>, startMarker: T)
  ensures
    StreamOfNonEmpties(Prepend(startMarker, M)) ==> // always holds, on account of Prepend_Lemma;
                                          // but until (co-)method can be called from functions,
                                          // this condition is used as an antecedent here
    FlattenStartMarker(M, startMarker) == FlattenNonEmpties(Prepend(startMarker, M));
{
  Prepend_Lemma(startMarker, M);
  Lemma_Flatten(Nil, M, startMarker);
}

greatest lemma Lemma_Flatten<T>(prefix: Stream, M: Stream<Stream>, startMarker: T)
  ensures
    StreamOfNonEmpties(Prepend(startMarker, M)) ==> // always holds, on account of Prepend_Lemma;
                                          // but until (co-)method can be called from functions,
                                          // this condition is used as an antecedent here
    PrependThenFlattenStartMarker(prefix, M, startMarker) == PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, M));
{
  Prepend_Lemma(startMarker, M);
  match (prefix) {
    case Cons(hd, tl) =>
      assert PrependThenFlattenStartMarker(tl, M, startMarker) == PrependThenFlattenNonEmpties(tl, Prepend(startMarker, M));
      Lemma_Flatten(tl, M, startMarker);
      assert PrependThenFlattenStartMarker(prefix, M, startMarker) == Cons(hd, PrependThenFlattenStartMarker(tl, M, startMarker));
      assert PrependThenFlattenNonEmpties(prefix, Prepend(star
function abs(a: real) : real {if a>0.0 then a else -a}
