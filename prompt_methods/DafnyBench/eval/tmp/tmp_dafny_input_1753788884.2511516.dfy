// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma TestMap(a: map<int, (int,int)>) {
  // The following assertion used to not prove automatically
  assert (map k | k in a :: a[k].0) == (map k | k in a :: a[k].0);
}

lemma TestSet0(a: set<int>) {
  // the following set comprehension implicitly uses k as the term
  assert (set k | k in a && k < 7) == (set k | k in a && k < 7);
}

lemma TestSet1(a: set<int>, m: int) {
  // the following set comprehension implicitly uses k as the term
  assert (set k | k in a && k < 7 :: m + (k - m)) == (set k | k in a && k < 7 :: m + (k - m));
}

lemma TestSet2(a: set<int>, m: int)
  requires m in a && m < 7
{
  // the following set comprehension implicitly uses k as the term
  assert (set k | k in a :: if k < 7 then k else m) == (set k | k in a :: if k < 7 then k else m);
}
function abs(a: real) : real {if a>0.0 then a else -a}
