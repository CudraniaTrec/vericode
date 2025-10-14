// RUN: %dafny /proverOpt:O:smt.qi.eager_threshold=30 /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file is a Dafny encoding of chapter 3 from "Concrete Semantics: With Isabelle/HOL" by
// Tobias Nipkow and Gerwin Klein.

// ----- lists -----

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

ghost function append(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, append(tail, ys))
}

// ----- arithmetic expressions -----

type vname = string  // variable names
datatype aexp = N(n: int) | V(vname) | Plus(aexp, aexp)  // arithmetic expressions

type val = int
type state = vname -> val

ghost function aval(a: aexp, s: state): val
{
  match a
  case N(n) => n
  case V(x) => s(x)
  case Plus(a0, a1) => aval(a0, s) + aval(a1, s)
}

lemma Example0()
{
  var y := aval(Plus(N(3), V("x")), x => 0);
  assert y == 3;
}

// ----- constant folding -----

ghost function asimp_const(a: aexp): aexp
{
  match a
  case N(n) => a
  case V(x) => a
  case Plus(a0, a1) =>
    var as0 := asimp_const(a0);
    var as1 := asimp_const(a1);
    if as0.N? && as1.N? then
      N(as0.n + as1.n)
    else
      Plus(as0, as1)
}

lemma AsimpConst(a: aexp, s: state)
  ensures aval(asimp_const(a), s) == aval(a, s)
{
  match a
  case N(n) =>
    assert asimp_const(a) == a;
    assert aval(asimp_const(a), s) == n;
    assert aval(a, s) == n;
  case V(x) =>
    assert asimp_const(a) == a;
    assert aval(asimp_const(a), s) == s(x);
    assert aval(a, s) == s(x);
  case Plus(a0, a1) =>
    AsimpConst(a0, s);
    AsimpConst(a1, s);
    var as0 := asimp_const(a0);
    var as1 := asimp_const(a1);
    if as0.N? && as1.N? {
      assert aval(N(as0.n + as1.n), s) == as0.n + as1.n;
      assert aval(as0, s) == aval(a0, s);
      assert aval(as1, s) == aval(a1, s);
      assert aval(N(as0.n + as1.n), s) == aval(a0, s) + aval(a1, s);
    } else {
      assert aval(Plus(as0, as1), s) == aval(as0, s) + aval(as1, s);
      assert aval(as0, s) == aval(a0, s);
      assert aval(as1, s) == aval(a1, s);
      assert aval(Plus(as0, as1), s) == aval(a0, s) + aval(a1, s);
    }
}

// more constant folding

ghost function plus(a0: aexp, a1: aexp): aexp
{
  if a0.N? && a1.N? then
    N(a0.n + a1.n)
  else if a0.N? then
    if a0.n == 0 then a1 else Plus(a0, a1)
  else if a1.N? then
    if a1.n == 0 then a0 else Plus(a0, a1)
  else
    Plus(a0, a1)
}

lemma AvalPlus(a0: aexp, a1: aexp, s: state)
  ensures aval(plus(a0, a1), s) == aval(a0, s) + aval(a1, s)
{
  if a0.N? && a1.N? {
    assert plus(a0, a1).N?;
    assert plus(a0, a1).n == a0.n + a1.n;
    assert aval(plus(a0, a1), s) == a0.n + a1.n;
    assert a0.n == aval(a0, s);
    assert a1.n == aval(a1, s);
  } else if a0.N? {
    if a0.n == 0 {
      assert plus(a0, a1) == a1;
      assert aval(plus(a0, a1), s) == aval(a1, s);
      assert aval(a0, s) == 0;
    } else {
      assert plus(a0, a1) == Plus(a0, a1);
      assert aval(plus(a0, a1), s) == aval(a0, s) + aval(a1, s);
    }
  } else if a1.N? {
    if a1.n == 0 {
      assert plus(a0, a1) == a0;
      assert aval(plus(a0, a1), s) == aval(a0, s);
      assert aval(a1, s) == 0;
    } else {
      assert plus(a0, a1) == Plus(a0, a1);
      assert aval(plus(a0, a1), s) == aval(a0, s) + aval(a1, s);
    }
  } else {
    assert plus(a0, a1) == Plus(a0, a1);
    assert aval(plus(a0, a1), s) == aval(a0, s) + aval(a1, s);
  }
}

ghost function asimp(a: aexp): aexp
{
  match a
  case N(n) => a
  case V(x) => a
  case Plus(a0, a1) => plus(asimp(a0), asimp(a1))
}

lemma AsimpCorrect(a: aexp, s: state)
  ensures aval(asimp(a), s) == aval(a, s)
{
  match a
  case N(n) =>
    assert asimp(a) == a;
    assert aval(asimp(a), s) == n;
    assert aval(a, s) == n;
  case V(x) =>
    assert asimp(a) == a;
    assert aval(asimp(a), s) == s(x);
    assert aval(a, s) == s(x);
  case Plus(a0, a1) =>
    AsimpCorrect(a0, s);
    AsimpCorrect(a1, s);
    assert asimp(a) == plus(asimp(a0), asimp(a1));
    AvalPlus(asimp(a0), asimp(a1), s);
    assert aval(asimp(a), s) == aval(plus(asimp(a0), asimp(a1)), s);
    assert aval(plus(asimp(a0), asimp(a1)), s) == aval(asimp(a0), s) + aval(asimp(a1), s);
    assert aval(asimp(a0), s) == aval(a0, s);
    assert aval(asimp(a1), s) == aval(a1, s);
    assert aval(asimp(a), s) == aval(a, s);
}

// The following lemma is not in the Nipkow and Klein book, but it's a fun one to prove.
lemma ASimplInvolutive(a: aexp)
  ensures asimp(asimp(a)) == asimp(a)
{
  match a
  case N(n) =>
    assert asimp(a) == a;
    assert asimp(asimp(a)) == asimp(a);
  case V(x) =>
    assert asimp(a) == a;
    assert asimp(asimp(a)) == asimp(a);
  case Plus(a0, a1) =>
    ASimplInvolutive(a0);
    ASimplInvolutive(a1);
    assert asimp(a) == plus(asimp(a0), asimp(a1));
    assert asimp(asimp(a)) == asimp(plus(asimp(a0), asimp(a1)));
    // asimp is idempotent on asimp(a0) and asimp(a1)
    // so asimp(plus(asimp(a0), asimp(a1))) == plus(asimp(a0), asimp(a1))
    // so asimp(asimp(a)) == asimp(a)
}

// ----- boolean expressions -----

datatype bexp = Bc(v: bool) | Not(bexp) | And(bexp, bexp) | Less(aexp, aexp)

ghost function bval(b: bexp, s: state): bool
{
  match b
  case Bc(v) => v
  case Not(b) => !bval(b, s)
  case And(b0, b1) => bval(b0, s) && bval(b1, s)
  case Less(a0, a1) => aval(a0, s) < aval(a1, s)
}

// constant folding for booleans

ghost function not(b: bexp): bexp
{
  match b
  case Bc(b0) => Bc(!b0)
  case Not(b0) => b0  // this case is not in the Nipkow and Klein book, but it seems a nice one to include
  case And(_, _) => Not(b)
  case Less(_, _) => Not(b)
}

ghost function and(b0: bexp, b1: bexp): bexp
{
  if b0.Bc? then
    if b0.v then b1 else b0
  else if b1.Bc? then
    if b1.v then b0 else b1
  else
    And(b0, b1)
}

ghost function less(a0: aexp, a1: aexp): bexp
{
  if a0.N? && a1.N? then
    Bc(a0.n < a1.n)
  else
    Less(a0, a1)
}

ghost function bsimp(b: bexp): bexp
{
  match b
  case Bc(v) => b
  case Not(b0) => not(bsimp(b0))
  case And(b0, b1) => and(bsimp(b0), bsimp(b1))
  case Less(a0, a1) => less(asimp(a0), asimp(a1))
}

lemma BsimpCorrect(b: bexp, s: state)
  ensures bval(bsimp(b), s) == bval(b, s)
{
  match b
  case Bc(v) =>
    assert bsimp(b) == b;
    assert bval(bsimp(b), s) == v;
    assert bval(b, s) == v;
  case Not(b0) =>
    BsimpCorrect(b0, s);
    assert bsimp(b) == not(bsimp(b0));
    if bsimp(b0).Bc? {
      assert not(bsimp(b0)) == Bc(!bsimp(b0).v);
      assert bval(not(bsimp(b0)), s) == !bsimp(b0).v;
      assert bval(bsimp(b0), s) == bval(b0, s);
      assert !bval(b0, s) == bval(b, s);
    } else if bsimp(b0).Not? {
      assert not(bsimp(b0)) == bsimp(b0).bexp;
      assert bval(not(bsimp(b0)), s) == bval(bsimp(b0).bexp, s);
    } else {
      assert bval(not(bsimp(b0)), s) == !bval(bsimp(b0), s);
      assert bval(bsimp(b0), s) == bval(b0, s);
      assert !bval(b0, s) == bval(b, s);
    }
  case And(b0, b1) =>
    BsimpCorrect(b0, s); BsimpCorrect(b1, s);
    assert bsimp(b) == and(bsimp(b0), bsimp(b1));
    if bsimp(b0).Bc? {
      if bsimp(b0).v {
        assert and(bsimp(b0), bsimp(b1)) == bsimp(b1);
        assert bval(and(bsimp(b0), bsimp(b1)), s) == bval(bsimp(b1), s);
        assert bval(bsimp(b1), s) == bval(b1, s);
        assert bval(b0, s) == true;
        assert bval(b, s) == bval(b1, s);
      } else {
        assert and(bsimp(b0), bsimp(b1)) == bsimp(b0);
        assert bval(and(bsimp(b0), bsimp(b1)), s) == bval(bsimp(b0), s);
        assert bval(bsimp(b0), s) == bval(b0, s);
        assert bval(b, s) == false;
      }
    } else if bsimp(b1).Bc? {
      if bsimp(b1).v {
        assert and(bsimp(b0), bsimp(b1)) == bsimp(b0);
        assert bval(and(bsimp(b0), bsimp(b1)), s) == bval(bsimp(b0), s);
        assert bval(bsimp(b0), s) == bval(b0, s);
        assert bval(b, s) == bval(b0, s);
      } else {
        assert and(bsimp(b0), bsimp(b1)) == bsimp(b1);
        assert bval(and(bsimp(b0), bsimp(b1)), s) == bval(bsimp(b1), s);
        assert bval(bsimp(b1), s) == bval(b1, s);
        assert bval(b, s) == false;
      }
    } else {
      assert and(bsimp(b0), bsimp(b1)) == And(bsimp(b0), bsimp(b1));
      assert bval(and(bsimp(b0), bsimp(b1)), s) == bval(bsimp(b0), s) && bval(bsimp(b1), s);
      assert bval(bsimp(b0), s) == bval(b0, s);
      assert bval(bsimp(b1), s) == bval(b1, s);
      assert bval(b, s) == bval(b0, s) && bval(b1, s);
    }
  case Less(a0, a1) =>
    AsimpCorrect(a0, s); AsimpCorrect(a1, s);
    assert bsimp(b) == less(asimp(a0), asimp(a1));
    if asimp(a0).N? && asimp(a1).N? {
      assert less(asimp(a0), asimp(a1)) == Bc(asimp(a0).n < asimp(a1).n);
      assert bval(less(asimp(a0), asimp(a1)), s) == asimp(a0).n < asimp(a1).n;
      assert aval(asimp(a0), s) == aval(a0, s);
      assert aval(asimp(a1), s) == aval(a1, s);
      assert bval(b, s) == aval(a0, s) < aval(a1, s);
    } else {
      assert less(asimp(a0), asimp(a1)) == Less(asimp(a0), asimp(a1));
      assert bval(less(asimp(a0), asimp(a1)), s) == aval(asimp(a0), s) < aval(asimp(a1), s);
      assert aval(asimp(a0), s) == aval(a0, s);
      assert aval(asimp(a1), s) == aval(a1, s);
      assert bval(b, s) == aval(a0, s) < aval(a1, s);
    }
}

// ----- stack machine -----

datatype instr = LOADI(val) | LOAD(vname) | ADD

type stack = List<val>

ghost function exec1(i: instr, s: state, stk: stack): stack
{
  match i
  case LOADI(n) => Cons(n, stk)
  case LOAD(x) => Cons(s(x), stk)
  case ADD =>
    if stk.Cons? && stk.tail.Cons? then
      var Cons(a1, Cons(a0, tail)) := stk;
      Cons(a0 + a1, tail)
    else  // stack underflow
      Nil  // an alternative would be to return Cons(n, Nil) for an arbitrary value n--that is what Nipkow and Klein do
}

ghost function exec(ii: List<instr>, s: state, stk: stack): stack
{
  match ii
  case Nil => stk
  case Cons(i, rest) => exec(rest, s, exec1(i, s, stk))
}

// ----- compilation -----

ghost function comp(a: aexp): List<instr>
{
  match a
  case N(n) => Cons(LOADI(n), Nil)
  case V(x) => Cons(LOAD(x), Nil)
  case Plus(a0, a1) => append(append(comp(a0), comp(a1)), Cons(ADD, Nil))
}

lemma CorrectCompilation(a: aexp, s: state, stk: stack)
  ensures exec(comp(a), s, stk) == Cons(aval(a, s), stk)
{
  match a
  case N(n) =>
    assert comp(a) == Cons(LOADI(n), Nil);
    assert exec(comp(a), s, stk) == exec(Cons(LOADI(n), Nil), s, stk);
    assert exec1(LOADI(n), s, stk) == Cons(n, stk);
    assert exec(Nil, s, Cons(n, stk)) == Cons(n, stk);
    assert exec(comp(a), s, stk) == Cons(n, stk);
    assert aval(a, s) == n;
  case V(x) =>
    assert comp(a) == Cons(LOAD(x), Nil);
    assert exec(comp(a), s, stk) == exec(Cons(LOAD(x), Nil), s, stk);
    assert exec1(LOAD(x), s, stk) == Cons(s(x), stk);
    assert exec(Nil, s, Cons(s(x), stk)) == Cons(s(x), stk);
    assert exec(comp(a), s, stk) == Cons(s(x), stk);
    assert aval(a, s) == s(x);
  case Plus(a0, a1) =>
    CorrectCompilation(a0, s, stk);
    CorrectCompilation(a1, s, Cons(aval(a0, s), stk));
    ExecAppend(comp(a0), comp(a1), s, stk);
    ExecAppend(append(comp(a0), comp(a1)), Cons(ADD, Nil), s, stk);
    assert exec(comp(a), s, stk)
      == exec(append(append(comp(a0), comp(a1)), Cons(ADD, Nil
function abs(a: real) : real {if a>0.0 then a else -a}
