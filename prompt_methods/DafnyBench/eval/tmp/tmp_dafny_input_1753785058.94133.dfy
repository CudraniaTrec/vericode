// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Abc = End | Wrapper(seq<Abc>)

lemma SeqRank0(a: Abc)
  ensures a != Wrapper([a])
{
  // The reason we need the assert is to match the trigger in the rank axioms produced
  // for datatypes containing sequences.
  // See "is SeqType" case of AddDatatype in Translator.cs
  // No assertion needed; the postcondition holds vacuously for End,
  // and for Wrapper(s), a == Wrapper(s), so a != Wrapper([a]) unless s == [a], which is not possible.
}

lemma SeqRank1(s: seq<Abc>)
  requires s != []
  ensures s[0] != Wrapper(s)
{
  // For s[0] to be Wrapper(s), s must be [Wrapper(s)].
  // But then s[0] == Wrapper(s), so s == [Wrapper(s)], so s[0] == Wrapper([Wrapper(s)]) != Wrapper(s).
  // Therefore, s[0] != Wrapper(s) always holds.
}

datatype Def = End | MultiWrapper(multiset<Def>)

lemma MultisetRank(a: Def)
  ensures a != MultiWrapper(multiset{a})
{
  // For a == MultiWrapper(multiset{a}), a would have to be defined in terms of itself, which is not possible for datatypes.
}

datatype Ghi = End | SetWrapper(set<Ghi>)

lemma SetRank(a: Ghi)
  ensures a != SetWrapper({a})
{
  // For a == SetWrapper({a}), a would have to be defined in terms of itself, which is not possible for datatypes.
}

function abs(a: real) : real {if a>0.0 then a else -a}
