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
      assert s != [a];
}

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
  match s[0]
    case End =>
    case Wrapper(t) =>
      assert t != s;
}

datatype Def = End | MultiWrapper(multiset<Def>)

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
  match a
    case End =>
    case MultiWrapper(m) =>
      assert m != multiset{a};
}

datatype Ghi = End | SetWrapper(set<Ghi>)

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
  match a
    case End =>
    case SetWrapper(s) =>
      assert s != {a};
}

function abs(a: real) : real {if a>0.0 then a else -a}
