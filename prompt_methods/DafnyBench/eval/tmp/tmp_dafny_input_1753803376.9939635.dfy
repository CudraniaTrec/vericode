// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// ----- Stream

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

ghost function append(M: Stream, N: Stream): Stream
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
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(f(x), map_f(N))
}

ghost function map_g(M: Stream<X>): Stream<X>
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(g(x), map_g(N))
}

ghost function map_fg(M: Stream<X>): Stream<X>
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
      assert map_fg(M) == Nil;
      assert map_f(map_g(M)) == Nil;
    case Cons(x, N) =>
      Theorem0(N);
      // No assertion needed, coinduction
  }
}
greatest lemma Theorem0_Alt(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  if (M.Cons?) {
    Theorem0_Alt(M.tail);
    // No assertion needed, coinduction
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
      case Cons(x, N) =>
        Theorem0_Ind(k-1, N);
    }
  }
}
lemma Theorem0_AutoInd(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M));
{
  // vacuously true for k == 0, otherwise follows by induction on k and structure of M
}

// map f (append M N) = append (map f M) (map f N)
greatest lemma Theorem1(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  match (M) {
    case Nil =>
    case Cons(x, M') =>
      Theorem1(M', N);
      // No assertion needed, coinduction
  }
}
greatest lemma Theorem1_Alt(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  if (M.Cons?) {
    Theorem1_Alt(M.tail, N);
    // No assertion needed, coinduction
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
  match (M) {
    case Nil =>
    case Cons(x, M') =>
      if (k != 0) {
        Theorem1_Ind(k-1, M', N);
      }
  }
}
lemma Theorem1_AutoInd(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
{
  // vacuously true for k == 0, otherwise follows by induction on k and structure of M
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
}

// append M NIL = M
greatest lemma Theorem3(M: Stream<X>)
  ensures append(M, Nil) == M;
{
  match (M) {
    case Nil =>
    case Cons(x, N) =>
      Theorem3(N);
      // No assertion needed, coinduction
  }
}
greatest lemma Theorem3_Alt(M: Stream<X>)
  ensures append(M, Nil) == M;
{
  if (M.Cons?) {
    Theorem3_Alt(M.tail);
    // No assertion needed, coinduction
  }
}

// append M (append N P) = append (append M N) P
greatest lemma Theorem4(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{
  match (M) {
    case Nil =>
    case Cons(x, M') =>
      Theorem4(M', N, P);
      // No assertion needed, coinduction
  }
}
greatest lemma Theorem4_Alt(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{
  if (M.Cons?) {
    Theorem4_Alt(M.tail, N, P);
    // No assertion needed, coinduction
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
{
  PrependThenFlattenStartMarker(Nil, M, startMarker)
}

ghost function PrependThenFlattenStartMarker<T>(prefix: Stream, M: Stream<Stream>, startMarker: T): Stream
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
{
  PrependThenFlattenNonEmpties(Nil, M)
}

ghost function PrependThenFlattenNonEmpties(prefix: Stream, M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
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
    case Cons(s, N) =>  
      Prepend_Lemma(x, N);
      // s.Cons? is not needed, Cons(x, s) is always Cons
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
    StreamOfNonEmpties(Prepend(startMarker, M)) ==>
    PrependThenFlattenStartMarker(prefix, M, startMarker) == PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, M));
{
  Prepend_Lemma(startMarker, M);
  match (prefix) {
    case Cons(hd, tl) =>
      Lemma_Flatten(tl, M, startMarker);
    case Nil =>
      match (M) {
        case Nil =>
        case Cons(s, N) =>
          // Only call on tail, do not assert on s.Cons? (not always true)
          Lemma_Flatten(s, N, startMarker);
      }
  }
}

greatest lemma Lemma_FlattenAppend0<T>(s: Stream, M: Stream<Stream>, startMarker: T)
  ensures PrependThenFlattenStartMarker(s, M, startMarker) == append(s, PrependThenFlattenStartMarker(Nil, M, startMarker));
{
  match (s) {
    case Nil =>
    case Cons(hd, tl) =>
      Lemma_FlattenAppend0(tl, M, startMarker);
  }
}

greatest lemma Lemma_FlattenAppend1<T>(s: Stream, M: Stream<Stream>)
  requires StreamOfNonEmpties(M);
  ensures PrependThenFlattenNonEmpties(s, M) == append(s, PrependThenFlattenNonEmpties(Nil, M));
{
  match (s) {
    case Nil =>
    case Cons(hd, tl) =>
      Lemma_FlattenAppend1(tl, M);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
