
// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma Tests<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures !z
{
  if {
    case true =>
      // 72 is not in 0..9
      assert forall i :: 0 <= i < 10 ==> i != 72;
      z := 72 in set i | 0 <= i < 10;
      assert !z;
    case true =>
      // -8 is not a nat, so not in k: nat | k < 10
      assert forall k: nat :: k < 10 ==> k != -8;
      z := -8 in set k: nat | k < 10;
      assert !z;
    case true =>
      // 6+1=7, so 7 is not in the set, so 6 not in set m | 0 <= m < 10 && Even(m) :: m+1
      assert forall m :: 0 <= m < 10 && Even(m) ==> m+1 != 6;
      z := 6 in set m | 0 <= m < 10 && Even(m) :: m + 1;
      assert !z;
    case true =>
      // t == uu[4], and t in uu, so t in set u | u in uu, so t !in ... is false
      assert t in set u | u in uu;
      z := t !in set u | u in uu;
      assert !z;
    case true =>
      // t == uu[4], so Id(t) == t, so t in set u | u in uu :: Id(u)
      assert t in set u {:autotriggers false} | u in uu :: Id(u);
      z := t !in set u {:autotriggers false} | u in uu :: Id(u);
      assert !z;
  }
}

lemma TestsWhereTriggersMatter<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures z
{
  if {
    case true =>
      // 7 in 0..9
      assert 0 <= 7 < 10;
      z := 7 in set i | 0 <= i < 10;
      assert z;
    case true =>
      // 8 is nat, 8 < 10
      assert 8 < 10;
      z := 8 in set k: nat | k < 10;
      assert z;
    case true =>
      // 5 is odd, but 4 is even and 4+1=5, so 5 in set m | 0 <= m < 10 && Even(m) :: m+1
      assert 0 <= 4 < 10 && Even(4) && 4+1 == 5;
      z := 5 in set m | 0 <= m < 10 && Even(m) :: m + 1;
      assert z;
      // a necessary lemma:
    case true =>
      // t == uu[4], so t in uu
      assert t in set u | u in uu;
      z := t in set u | u in uu;
      assert z;
    case true =>
      // t == uu[4], so Id(t) == t, so t in set u | u in uu :: Id(u)
      assert t in set u {:autotriggers false} | u in uu :: Id(u);
      z := t in set u {:autotriggers false} | u in uu :: Id(u);
      assert z;
  }
}

function Id<T>(t: T): T { t }
predicate Even(x: int) { x % 2 == 0 }

class Container<T> {
  ghost var Contents: set<T>
  var elems: seq<T>

  method Add(t: T)
    requires Contents == set x | x in elems
    modifies this
    ensures Contents == set x | x in elems
  {
    // Invariant: Contents == set x | x in elems
    var oldElems := elems;
    var oldContents := Contents;
    elems := elems + [t];
    Contents := Contents + {t};
    assert Contents == set x | x in elems;
    assert elems == oldElems + [t];
    assert Contents == oldContents + {t};
  }
}

class IntContainer {
  ghost var Contents: set<int>
  var elems: seq<int>

  method Add(t: int)
    requires Contents == set x | x in elems
    modifies this
    ensures Contents == set x | x in elems
  {
    // Invariant: Contents == set x | x in elems
    var oldElems := elems;
    var oldContents := Contents;
    elems := elems + [t];
    Contents := Contents + {t};
    assert Contents == set x | x in elems;
    assert elems == oldElems + [t];
    assert Contents == oldContents + {t};
  }
}

method UnboxedBoundVariables(si: seq<int>)
{
  var iii := set x | x in si;
  var ti := si + [115];
  var jjj := set y | y in ti;

  var nnn := set n: nat | n in si;
  // loop invariant: forall i :: 0 <= i < |si| ==> 0 <= si[i]
  if forall i :: 0 <= i < |si| ==> 0 <= si[i] {
    assert forall n: nat :: n in si ==> 0 <= n;
    assert forall i :: 0 <= i < |si| ==> si[i] in nnn;
    assert forall n: nat :: n in nnn ==> n in iii;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
