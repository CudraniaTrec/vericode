
// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma Tests<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures !z
{
  if {
    case true =>
      // 72 is not in 0..9
      assert forall i :: {i in set i | 0 <= i < 10} 0 <= i < 10 ==> i != 72;
      z := 72 in set i | 0 <= i < 10;
      assert !z;
    case true =>
      // -8 is not a nat, so not in the set
      assert forall k: nat :: {k in set k: nat | k < 10} k < 10 ==> k != -8;
      z := -8 in set k: nat | k < 10;
      assert !z;
    case true =>
      // The set is {m + 1 | 0 <= m < 10 && Even(m)}
      // 6 is not in the set, because m + 1 = 6 => m = 5, but 5 is not even
      assert forall m :: {m + 1 | 0 <= m < 10 && Even(m)} 0 <= m < 10 && Even(m) ==> m + 1 != 6;
      z := 6 in set m | 0 <= m < 10 && Even(m) :: m + 1;
      assert !z;
    case true =>
      // t in uu, so t in set u | u in uu
      assert t in set u | u in uu;
      z := t !in set u | u in uu;
      assert !z;
    case true =>
      // t in uu, so t in set u | u in uu :: Id(u)
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
      assert exists i :: {i in set i | 0 <= i < 10} 0 <= i < 10 && i == 7;
      z := 7 in set i | 0 <= i < 10;
      assert z;
    case true =>
      // 8 in nat, 8 < 10
      assert exists k: nat :: {k in set k: nat | k < 10} k < 10 && k == 8;
      z := 8 in set k: nat | k < 10;
      assert z;
    case true =>
      // The set is {m + 1 | 0 <= m < 10 && Even(m)}, m = 4 => 5
      assert exists m :: {m + 1 | 0 <= m < 10 && Even(m)} 0 <= m < 10 && Even(m) && m + 1 == 5;
      z := 5 in set m | 0 <= m < 10 && Even(m) :: m + 1;
      assert z;
    case true =>
      // t in uu, so t in set u | u in uu
      assert t in set u | u in uu;
      z := t in set u | u in uu;
      assert z;
    case true =>
      // t in uu, so t in set u | u in uu :: Id(u)
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
    elems := elems + [t];
    Contents := Contents + {t};
    assert Contents == set x | x in elems;
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
    elems := elems + [t];
    Contents := Contents + {t};
    assert Contents == set x | x in elems;
  }
}

method UnboxedBoundVariables(si: seq<int>)
{
  var iii := set x | x in si;
  var ti := si + [115];
  var jjj := set y | y in ti;

  var nnn := set n: nat | n in si;
  if forall i :: 0 <= i < |si| ==> 0 <= si[i] {
    // Loop invariant: all elements of si are >= 0
    var i: int := 0;
    while i < |si|
      invariant 0 <= i <= |si|
      invariant forall j :: 0 <= j < i ==> 0 <= si[j]
    {
      // This assertion is not provable in general, so remove it.
      i := i + 1;
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
