// RUN: %dafny /compile:0 /deprecation:0 /proverOpt:O:smt.qi.eager_threshold=30 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This is the Extractor Problem from section 11.8 of the ACL2 book,
// "Computer-Aided Reasoning: An Approach" by Kaufmann, Manolios, and
// Moore (2011 edition).

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

ghost function length<T>(xs: List<T>): nat
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

ghost function append<T>(xs: List<T>, ys: List<T>): List<T>
{
  match xs
  case Nil => ys
  case Cons(x, rest) => Cons(x, append(rest, ys))
}

ghost function rev<T>(xs: List<T>): List<T>
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
  var a: List<T> := xtr(nats(length(xs)), xs);
  var b: List<T> := rev(xs);
  calc {
    length(a);
    { XtrLength<T>(nats(length(xs)), xs); }
    length(nats(length(xs)));
    { NatsLength(length(xs)); }
    length(xs);
  }
  calc {
    length(xs);
    { RevLength<T>(xs); }
    length(b);
  }
  forall i | 0 <= i < length(xs)
    ensures nth(i, a) == nth(i, b);
  {
    reveal nth();
    ExtractorLemma(i, xs);
  }
  EqualElementsMakeEqualLists(a, b);
}

// auxiliary lemmas and proofs follow

// lemmas about length

lemma XtrLength<T>(mp: List<int>, lst: List<T>)
  ensures length(xtr(mp, lst)) == length(mp);
{
  match mp {
    case Nil =>
    case Cons(n, rest) =>
      XtrLength<T>(rest, lst);
      assert length(xtr(mp, lst)) == 1 + length(xtr(rest, lst));
      assert length(mp) == 1 + length(rest);
  }
}

lemma NatsLength(n: nat)
  ensures length(nats(n)) == n;
{
  if n == 0 {
  } else {
    NatsLength(n-1);
    assert length(nats(n)) == 1 + length(nats(n-1));
  }
}

lemma AppendLength<T>(xs: List<T>, ys: List<T>)
  ensures length(append(xs, ys)) == length(xs) + length(ys);
{
  match xs {
    case Nil =>
      assert length(append(Nil, ys)) == length(ys);
      assert length(Nil) == 0;
    case Cons(x, rest) =>
      AppendLength(rest, ys);
      assert length(append(xs, ys)) == 1 + length(append(rest, ys));
      assert length(xs) == 1 + length(rest);
  }
}

lemma RevLength<T>(xs: List<T>)
  ensures length(rev(xs)) == length(xs);
{
  match xs {
    case Nil =>
    case Cons(x, rest) =>
      RevLength(rest);
      AppendLength(rev(rest), Cons(x, Nil));
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
      match ys {
        case Nil => assert false;
        case Cons(y, resty) =>
          assert nth(0, xs) == nth(0, ys);
          assert x == y;
          assert length(rest) == length(resty);
          forall i | 0 <= i < length(rest)
            ensures nth(i, rest) == nth(i, resty)
          {
            assert nth(i+1, xs) == nth(i+1, ys);
          }
          EqualElementsMakeEqualLists(rest, resty);
      }
  }
}

// here is the theorem, but applied to the ith element

lemma {:vcs_split_on_every_assert} ExtractorLemma<T(00)>(i: int, xs: List<T>)
  requires 0 <= i < length(xs);
  ensures nth(i, xtr(nats(length(xs)), xs)) == nth(i, rev(xs));
{
  calc {
    nth(i, xtr(nats(length(xs)), xs));
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
  ensures nth(i, xtr(mp, lst)) == nth(nth(i, mp), lst);
{
  reveal nth();
  XtrLength<T>(mp, lst);
  match mp {
    case Nil =>
      assert false;
    case Cons(n, rest) =>
      if i == 0 {
        assert nth(0, xtr(mp, lst)) == nth(n, lst);
        assert nth(0, mp) == n;
      } else {
        NthXtr<T>(i-1, rest, lst);
        assert nth(i, xtr(mp, lst)) == nth(nth(i, mp), lst);
      }
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
    assert n > 0;
    assert nats(n) == Cons(n-1, nats(n-1));
    assert nthWorker(0, nats(n)) == n-1;
    assert n - 1 - 0 == n-1;
  } else {
    assert n > 0;
    assert nats(n) == Cons(n-1, nats(n-1));
    assert nthWorker(i, nats(n)) == nthWorker(i-1, nats(n-1));
    NthNatsWorker(i-1, n-1);
    assert nthWorker(i-1, nats(n-1)) == n-1 - (i-1);
    assert n - 1 - i == (n-1) - (i-1);
  }
}

lemma NthRev<T(00)>(i: int, xs: List<T>)
  requires 0 <= i < length(xs) == length(rev(xs));
  ensures nthWorker(i, rev(xs)) == nthWorker(length(xs) - 1 - i, xs);
{
  reveal nth();
  match xs {
    case Nil =>
      assert false;
    case Cons(x, rest) =>
      RevLength<T>(rest);
      var lenRest := length(rest);
      if i < lenRest {
        NthAppendA<T>(i, rev(rest), Cons(x, Nil));
        NthRev<T>(i, rest);
        assert nthWorker(i, rev(xs)) == nthWorker(lenRest - 1 - i, rest);
        assert nthWorker(lenRest - 1 - i + 1, xs) == nthWorker(length(xs) - 1 - i, xs);
      } else {
        NthAppendB<T>(i, rev(rest), Cons(x, Nil));
        assert i - lenRest == 0;
        assert nthWorker(i - lenRest, Cons(x, Nil)) == x;
        assert nthWorker(0, xs) == x;
        assert length(xs) == lenRest + 1;
        assert length(xs) - 1 - lenRest == 0;
      }
  }
}

lemma NthAppendA<T(00)>(i: int, xs: List<T>, ys: List<T>)
  requires 0 <= i < length(xs);
  ensures nth(i, append(xs, ys)) == nth(i, xs);
{
  reveal nth();
  match xs {
    case Nil =>
      assert false;
    case Cons(x, rest) =>
      if i == 0 {
        assert append(xs, ys) == Cons(x, append(rest, ys));
        assert nth(0, append(xs, ys)) == x;
        assert nth(0, xs) == x;
      } else {
        NthAppendA<T>(i-1, rest, ys);
        assert nth(i, append(xs, ys)) == nth(i, Cons(x, append(rest, ys)));
        assert nth(i, Cons(x, append(rest, ys))) == nth(i-1, append(rest, ys));
        assert nth(i-1, append(rest, ys)) == nth(i-1, rest);
        assert nth(i, xs) == nth(i-1, rest);
      }
  }
}

lemma NthAppendB<T(00)>(i: int, xs: List<T>, ys: List<T>)
  requires length(xs) <= i < length(xs) + length(ys);
  ensures nth(i, append(xs, ys)) == nth(i - length(xs), ys);
{
  reveal nth();
  AppendLength<T>(xs, ys);
  match xs {
    case Nil =>
      assert i - length(Nil) == i;
      assert append(Nil, ys) == ys;
      assert nth(i, append(Nil, ys)) == nth(i, ys);
    case Cons(x, rest) =>
      NthAppendB<T>(i-1, rest, ys);
      assert nth(i, append(xs, ys)) == nth(i-1, append(rest, ys));
      assert length(xs) == 1 + length(rest);
      assert i - length(xs) == i-1 - length(rest);
      assert nth(i-1, append(rest, ys)) == nth(i-1 - length(rest), ys);
      assert nth(i, append(xs, ys)) == nth(i - length(xs), ys);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
