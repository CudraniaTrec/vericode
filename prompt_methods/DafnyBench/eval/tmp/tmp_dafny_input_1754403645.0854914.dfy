
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype State = State(m:map<int, bool>)

lemma Test(s:State)
  requires 42 in s.m
  ensures s.(m := s.m[42 := s.m[42]]) == s
{
  var s' := s.(m := s.m[42 := s.m[42]]);
  assert s'.m == s.m; // strongest: map update with same value is identity
  assert s' == s;
}

datatype MyDt = MakeA(x: int, bool) | MakeB(s: multiset<int>, t: State)

lemma AnotherTest(a: MyDt, b: MyDt, c: bool)
  requires a.MakeB? && b.MakeB?
  requires a.s == multiset(a.t.m.Keys) && |b.s| == 0
  requires a.t.m == map[] && |b.t.m| == 0
{
  assert a.MakeB?;
  assert b.MakeB?;
  assert a.s == multiset(a.t.m.Keys);
  assert |b.s| == 0;
  assert a.t.m == map[];
  assert |b.t.m| == 0;
  assert a.s == multiset{}; // strongest: a.t.m.Keys is empty, so multiset is empty
}

datatype GenDt<X,Y> = Left(X) | Middle(X,int,Y) | Right(y: Y)

method ChangeGen(g: GenDt)
{
  match g
  case Left(_) =>
    assert g.Left?;
  case Middle(_,_,_) =>
    assert g.Middle?;
  case Right(u) =>
    assert g.Right?;
    var h := g.(y := u);
    assert h == g; // strongest: updating y to same value
}

datatype Recursive<X> = Red | Green(next: Recursive, m: set)

lemma RecLem(r: Recursive) returns (s: Recursive)
  ensures r == s
{
  match r
  case Red =>
    s := Red;
    assert s == r;
  case Green(next, m) =>
    var n := RecLem(next);
    assert n == next;
    s := Green(n, m + m);
    assert m + m == m; // strongest: set union with itself is itself
    assert s == Green(next, m);
    assert s == r;
}

function abs(a: real) : real {if a>0.0 then a else -a}
