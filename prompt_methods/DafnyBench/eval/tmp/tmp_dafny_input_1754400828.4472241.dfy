// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Abc = End | Wrapper(seq<Abc>)

lemma SeqRank0(a: Abc)
  ensures a != Wrapper([a])
{
  // The reason we need the assert is to match the trigger in the rank axioms produced
  // for datatypes containing sequences.
  // See "is SeqType" case of AddDatatype in Translator.cs
  match a
    case End =>
    case Wrapper(s) =>
      // a == Wrapper(s), so Wrapper([a]) == Wrapper(s) iff [a] == s
      // So a == Wrapper([a]) iff s == [a]
      // We cannot assert [a] != s in general, so no assertion here.
      // The postcondition is sufficient.
}

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
  // We cannot assert s[0] != Wrapper(s) in general, so no assertion here.
  // The postcondition is sufficient.
}

datatype Def = End | MultiWrapper(multiset<Def>)

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
  match a
    case End =>
    case MultiWrapper(s) =>
      // a == MultiWrapper(s), so MultiWrapper(multiset{a}) == MultiWrapper(s) iff multiset{a} == s
      // So a == MultiWrapper(multiset{a}) iff s == multiset{a}
      assert s != multiset{a};
}

datatype Ghi = End | SetWrapper(set<Ghi>)

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
  match a
    case End =>
    case SetWrapper(s) =>
      // a == SetWrapper(s), so SetWrapper({a}) == SetWrapper(s) iff {a} == s
      // So a == SetWrapper({a}) iff s == {a}
      assert s != {a};
}

function abs(a: real) : real {if a>0.0 then a else -a}
