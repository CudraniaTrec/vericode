// RUN: %dafny /compile:0 /deprecation:0 /proverOpt:O:smt.qi.eager_threshold=30 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This is the Extractor Problem from section 11.8 of the ACL2 book,
// "Computer-Aided Reasoning: An Approach" by Kaufmann, Manolios, and
// Moore (2011 edition).

datatype List<T> = Nil | Cons(head: T, tail: List)

ghost function length(xs: List): nat
{
  match xs
  case Nil => 0
  case Cons(_, rest) => 1 + length(rest)
}

// If "0 <= n < length(xs)", then return the element of "xs" that is preceded by
// "n" elements; otherwise, return an arbitrary value.
ghost opaque function nth<T(00)>(n: int, xs: List<T>): T
{
  if 0 <= n < length(xs) then
    nthWorker(n, xs)
  else
    var t :| true; t
}

ghost function nthWorker<T>(n: int, xs: List<T>): T
  requires 0 <= n < length(xs);
{
  if n == 0 then xs.head else nthWorker(n-1, xs.tail)
}

ghost function append(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x, rest) => Cons(x, append(rest, ys))
}

ghost function rev(xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(x, rest) => append(rev(rest), Cons(x, Nil))
}

ghost function nats(n: nat): List<int>
{
  if n == 0 then Nil else Cons(n-1, nats(n-1))
}

ghost function xtr<T(00)>(mp: List<int>, lst: List<T>): List<T>
{
  match mp
  case Nil => Nil
  case Cons(n, rest) => Cons(nth(n, lst), xtr(rest, lst))
}

lemma ExtractorTheorem<T(00)>(xs: List<T>)
  ensures xtr(nats(length(xs)), xs) == rev(xs);
{
  var a, b := xtr(nats(length(xs)), xs), rev(xs);
  calc {
    length(a);
    { XtrLength<T>(nats(length(xs)), xs); }
    length(nats(length(xs)));
    { NatsLength(length(xs)); }
    length(xs);
  }
  calc {
    length(xs);
    { RevLength(xs); }
    length(b);
  }
  forall i | 0 <= i < length(xs)
    ensures nth(i, a) == nth(i, b);
  {
    reveal nth();
    ExtractorLemma<T>(i, xs);
  }
  EqualElementsMakeEqualLists<T>(a, b);
}

// auxiliary lemmas and proofs follow

// lemmas about length

lemma XtrLength<T(00)>(mp: List<int>, lst: List<T>)
  ensures length(xtr<T>(mp, lst)) == length(mp);
{
  match mp
  case Nil =>
    assert length(xtr<T>(mp, lst)) == 0;
    assert length(mp) == 0;
  case Cons(n, rest) =>
    XtrLength<T>(rest, lst);
    assert length(xtr<T>(rest, lst)) == length(rest);
    assert length(xtr<T>(mp, lst)) == 1 + length(xtr<T>(rest, lst));
    assert length(mp) == 1 + length(rest);
    assert length(xtr<T>(mp, lst)) == length(mp);
}

lemma NatsLength(n: nat)
  ensures length(nats(n)) == n;
{
  if n == 0 {
    assert nats(n) == Nil;
    assert length(nats(n)) == 0;
  } else {
    NatsLength(n-1);
    assert length(nats(n-1)) == n-1;
    assert nats(n) == Cons(n-1, nats(n-1));
    assert length(nats(n)) == 1 + length(nats(n-1));
    assert length(nats(n)) == n;
  }
}

lemma AppendLength(xs: List, ys: List)
  ensures length(append(xs, ys)) == length(xs) + length(ys);
{
  match xs
  case Nil =>
    assert append(xs, ys) == ys;
    assert length(xs) == 0;
    assert length(append(xs, ys)) == length(ys);
    assert length(xs) + length(ys) == length(ys);
  case Cons(x, rest) =>
    AppendLength(rest, ys);
    assert length(append(rest, ys)) == length(rest) + length(ys);
    assert length(append(xs, ys)) == 1 + length(append(rest, ys));
    assert length(xs) == 1 + length(rest);
    assert length(append(xs, ys)) == length(xs) + length(ys);
}

lemma RevLength(xs: List)
  ensures length(rev(xs)) == length(xs);
{
  match xs {
    case Nil =>
      assert rev(xs) == Nil;
      assert length(rev(xs)) == 0;
      assert length(xs) == 0;
    case Cons(x, rest) =>
      RevLength(rest);
      AppendLength(rev(rest), Cons(x, Nil));
      assert length(rev(xs)) == length(append(rev(rest), Cons(x, Nil)));
      assert length(append(rev(rest), Cons(x, Nil))) == length(rev(rest)) + length(Cons(x, Nil));
      assert length(rev(rest)) == length(rest);
      assert length(Cons(x, Nil)) == 1;
      assert length(rev(xs)) == length(rest) + 1;
      assert length(xs) == 1 + length(rest);
      assert length(rev(xs)) == length(xs);
  }
}

// you can prove two lists equal by proving their elements equal

lemma EqualElementsMakeEqualLists<T(00)>(xs: List<T>, ys: List<T>)
  requires length(xs) == length(ys)
  requires forall i :: 0 <= i < length(xs) ==> nth(i, xs) == nth(i, ys)
  ensures xs == ys
{
  reveal nth();
  match xs {
    case Nil =>
      assert ys == Nil;
    case Cons(x, rest) =>
      assert ys != Nil;
      var y := ys.head;
      var ysTail := ys.tail;
      assert nth(0, xs) == nth(0, ys);
      assert x == y;
      assert length(xs.tail) == length(ys.tail);
      forall i | 0 <= i < length(xs.tail)
        ensures nth(i, xs.tail) == nth(i, ys.tail)
      {
        assert 0 <= i < length(xs.tail);
        assert nth(i+1, xs) == nth(i+1, ys);
        assert nth(i, xs.tail) == nth(i+1, xs);
        assert nth(i, ys.tail) == nth(i+1, ys);
      }
      EqualElementsMakeEqualLists<T>(xs.tail, ys.tail);
  }
}

// here is the theorem, but applied to the ith element

lemma {:vcs_split_on_every_assert} ExtractorLemma<T(00)>(i: int, xs: List<T>)
  requires 0 <= i < length(xs);
  ensures nth(i, xtr<T>(nats(length(xs)), xs)) == nth(i, rev(xs));
{
  calc {
    nth(i, xtr<T>(nats(length(xs)), xs));
    { NatsLength(length(xs));
      NthXtr<T>(i, nats(length(xs)), xs); }
    nth(nth(i, nats(length(xs))), xs);
    { NthNats(i, length(xs)); }
    nth(length(xs) - 1 - i, xs);
    { reveal nth(); RevLength(xs); NthRev<T>(i, xs); }
    nth(i, rev(xs));
  }
}

// lemmas about what nth gives on certain lists

lemma NthXtr<T(00)>(i: int, mp: List<int>, lst: List<T>)
  requires 0 <= i < length(mp);
  ensures nth(i, xtr<T>(mp, lst)) == nth(nth(i, mp), lst);
{
  reveal nth();
  XtrLength<T>(mp, lst);
  match mp
  case Nil =>
    // unreachable by precondition
    assert false;
  case Cons(n, rest) =>
    if i == 0 {
      assert xtr<T>(mp, lst) == Cons(nth(n, lst), xtr<T>(rest, lst));
      assert nth(0, xtr<T>(mp, lst)) == nth(n, lst);
      assert nth(0, mp) == n;
      assert nth(nth(0, mp), lst) == nth(n, lst);
    } else {
      assert xtr<T>(mp, lst) == Cons(nth(n, lst), xtr<T>(rest, lst));
      assert nth(i, xtr<T>(mp, lst)) == nth(i-1, xtr<T>(rest, lst));
      NthXtr<T>(i-1, rest, lst);
      assert nth(i-1, xtr<T>(rest, lst)) == nth(nth(i-1, rest), lst);
      assert nth(i, mp) == nth(i-1, rest);
      assert nth(i, xtr<T>(mp, lst)) == nth(nth(i, mp), lst);
    }
}

lemma NthNats(i: int, n: nat)
  requires 0 <= i < n;
  ensures nth(i, nats(n)) == n - 1 - i;
{
  reveal nth();
  NatsLength(n);
  NthNatsWorker(i, n);
}

lemma NthNatsWorker(i: int, n: nat)
  requires 0 <= i < n && length(nats(n)) == n;
  ensures nthWorker(i, nats(n)) == n - 1 - i;
{
  if i == 0 {
    assert nats(n) == Cons(n-1, nats(n-1));
    assert nthWorker(0, nats(n)) == nats(n).head;
    assert nats(n).head == n-1;
    assert n - 1 - 0 == n-1;
  } else {
    assert nats(n) == Cons(n-1, nats(n-1));
    assert nthWorker(i, nats(n)) == nthWorker(i-1, nats(n-1));
    assert 0 <= i-1 < n-1;
    assert length(nats(n-1)) == n-1;
    NthNatsWorker(i-1, n-1);
    assert nthWorker(i-1, nats(n-1)) == n-1-(i-1);
    assert n-1-(i-1) == n-1-i;
    assert nthWorker(i, nats(n)) == n-1-i;
  }
}

lemma NthRev<T(00)>(i: int, xs: List<T>)
  requires 0 <= i < length(xs) == length(rev(xs));
  ensures nthWorker(i, rev(xs)) == nthWorker(length(xs) - 1 - i, xs);
{
  reveal nth();
  RevLength(xs.tail);
  match xs
  case Nil =>
    // unreachable by precondition
    assert false;
  case Cons(x, rest) =>
    if i < length(rev(rest)) {
      calc {
        nth(i, rev(xs));
        nthWorker(i, rev(xs));
        // def. rev
        nthWorker(i, append(rev(rest), Cons(x, Nil)));
        { NthAppendA<T>(i, rev(rest), Cons(x, Nil)); }
        nthWorker(i, rev(rest));
        { NthRev<T>(i, rest); }
        nthWorker(length(rest) - 1 - i, rest);
        // def. nthWorker
        nthWorker(length(rest) - 1 - i + 1, xs);
        assert length(xs) == 1 + length(rest);
        nthWorker(length(xs) - 1 - i, xs);
      }
    } else {
      calc {
        nth(i, rev(xs));
        nthWorker(i, rev(xs));
        // def. rev
        nthWorker(i, append(rev(rest), Cons(x, Nil)));
        { NthAppendB<T>(i, rev(rest), Cons(x, Nil)); }
        nthWorker(i - length(rev(rest)), Cons(x, Nil));
        nthWorker(0, Cons(x, Nil));
        nthWorker(0, xs);
        nthWorker(length(xs) - 1 - length(rev(rest)), xs);
        { RevLength(rest); }
        nthWorker(length(xs) - 1 - length(rest), xs);
        assert length(xs) == 1 + length(rest);
        nthWorker(length(xs) - 1 - i, xs);
      }
    }
}

lemma NthAppendA<T(00)>(i: int, xs: List<T>, ys: List<T>)
  requires 0 <= i < length(xs);
  ensures nth(i, append(xs, ys)) == nth(i, xs);
{
  reveal nth();
  match xs
  case Nil =>
    // unreachable by precondition
    assert false;
  case Cons(x, rest) =>
    if i == 0 {
      calc {
        nth(0, append(xs, ys));
        nth(0, Cons(x, append(rest, ys)));
        x;
      }
      assert nth(0, xs) == x;
    } else {
      calc {
        nth(i, append(xs, ys));
        nth(i, Cons(x, append(rest, ys)));
        nth(i-1, append(rest, ys));
        { NthAppendA<T>(i-1, rest, ys); }
        nth(i-1, rest);
      }
      assert nth(i, xs) == nth(i-1, rest);
    }
}

lemma NthAppendB<T(00)>(i: int, xs: List<T>, ys: List<T>)
  requires length(xs) <= i < length(xs) + length(ys);
  ensures nth(i, append(xs, ys)) == nth(i - length(xs), ys);
{
  reveal nth();
  AppendLength(xs, ys);
  match xs
  case Nil =>
    assert append(xs, ys) == ys;
    assert length(xs) == 0;
    assert nth(i, append(xs, ys)) == nth(i, ys);
    assert nth(i - 0, ys) == nth(i, ys);
  case Cons(x, rest) =>
    assert length(xs) == 1 + length(rest);
    assert i >= 1 + length(rest);
    assert append(xs, ys) == Cons(x, append(rest, ys));
    assert nth(i, append(xs, ys)) == nth(i-1, append(rest, ys));
    NthAppendB<T>(i-1, rest, ys);
    assert nth(i-1, append(rest, ys)) == nth(i-1 - length(rest), ys);
    assert length(xs) == 1 + length(rest);
    assert i - length(xs) == (i-1) - length(rest);
    assert nth(i, append(xs, ys)) == nth(i - length(xs), ys);
}

function abs(a: real) : real {if a>0.0 then a else -a}
