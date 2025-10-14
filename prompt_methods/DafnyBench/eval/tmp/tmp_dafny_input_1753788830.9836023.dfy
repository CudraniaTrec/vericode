
// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate ContainsNothingBut5(s: set<int>)
{
  forall q :: q in s ==> q == 5
}

predicate YeahContains5(s: set<int>)
{
  exists q :: q in s && q == 5
}

predicate ViaSetComprehension(s: set<int>) {
  |set q | q in s && q == 5| != 0
}

predicate LambdaTest(s: set<int>) {
  (q => q in s)(5)
}

predicate ViaMapComprehension(s: set<int>) {
  |(map q | q in s && q == 5 :: true).Keys| != 0
}

predicate Contains5(s: set<int>)
{
  var q := 5; q in s
}

datatype R = MakeR(int) | Other

predicate RIs5(r: R) {
  match r case MakeR(q) => q == 5 case Other => false
}

lemma NonemptySet(x: int, s: set<int>)
  requires x in s
  ensures |s| != 0
{
  // Strongest annotation: |s| != 0 follows directly from x in s
  assert |s| != 0;
}

lemma NonemptyMap(x: int, s: map<int,bool>)
  requires x in s.Keys
  ensures |s| != 0
{
  // Strongest annotation: |s| != 0 follows directly from x in s.Keys
  assert |s| != 0;
}

method M(s: set<int>, r: R, q: int)
  requires s == {5} && r == MakeR(5)
{

  // s == {5}, so set q | q in s && q == 5 == {5}
  assert set q | q in s && q == 5 == {5};
  NonemptySet(5, set q | q in s && q == 5);

  // s == {5}, so map q | q in s && q == 5 :: true == map[5 := true]
  assert map q | q in s && q == 5 :: true == map[5 := true];
  NonemptyMap(5, map q | q in s && q == 5 :: true);

}

function abs(a: real) : real {if a>0.0 then a else -a}
