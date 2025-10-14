
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

// This file shows an example program that uses both refinement and :autocontracts
// specify a class that stores a set of things that can be retrieved using a query.
//
// (For another example that uses these features, see Test/dafny3/CachedContainer.dfy.)

abstract module AbstractInterface {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> {
    ghost var Contents: set<Thing>
    ghost predicate Valid() {
      Valid'()
    }
    ghost predicate {:autocontracts false} Valid'()
      reads this, Repr
    constructor Init()
      ensures Contents == {}
    method Store(t: Thing)
      ensures Contents == old(Contents) + {t}
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists t :: t in Contents && matchCriterion(t)
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
  }
}

abstract module A refines AbstractInterface {
  class StoreAndRetrieve<Thing(==)> ... {
    constructor Init...
    {
      Contents := {};
      Repr := {this};
      new;
      assume Valid'();  // to be checked in module B
    }
    method Store...
    {
      Contents := Contents + {t};
      assume Valid'();  // to be checked in module B
    }
    method Retrieve...
    {
      var k :| assume k in Contents && matchCriterion(k);
      thing := k;
    }
  }
}

abstract module B refines A {
  class StoreAndRetrieve<Thing(==)> ... {
    var arr: seq<Thing>
    ghost predicate Valid'...
    {
      Contents == set x | x in arr
    }
    constructor Init...
    {
      arr := [];
      new;
    }
    method Store...
    {
      arr := arr + [t];
      Contents := set x | x in arr;
      assert Valid'();
    }
    method Retrieve...
    {
      var i := 0;
      // Strongest possible invariant:
      // - 0 <= i <= |arr|
      // - forall j :: 0 <= j < i ==> !matchCriterion(arr[j])
      // - exists j :: i <= j < |arr| && matchCriterion(arr[j])
      // - arr is a sequence of distinct elements (if needed)
      // - Contents == set x | x in arr
      while (i < |arr|)
        invariant 0 <= i <= |arr|
        invariant forall j :: 0 <= j < i ==> !matchCriterion(arr[j])
        invariant exists j :: i <= j < |arr| && matchCriterion(arr[j])
        invariant Contents == set x | x in arr
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      assert i < |arr|; // because precondition guarantees existence
      var k := arr[i];
      thing := k;
      assert thing in Contents && matchCriterion(thing);
      assert Contents == old(Contents);
      var a: seq<Thing> :| assume Contents == set x | x in a;
      arr := a;
      Contents := set x | x in arr;
      assert Valid'();
    }
  }
}

module abC refines B { // TODO module C causes Go to fail
  class StoreAndRetrieve<Thing(==)> ... {
    method Retrieve...
    {
      // Inherited code up to here
      var i := 0;
      while (i < |arr|)
        invariant 0 <= i <= |arr|
        invariant forall j :: 0 <= j < i ==> !matchCriterion(arr[j])
        invariant exists j :: i <= j < |arr| && matchCriterion(arr[j])
        invariant Contents == set x | x in arr
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      assert i < |arr|;
      var k := arr[i];
      thing := k;
      assert thing in Contents && matchCriterion(thing);
      assert Contents == old(Contents);
      var a := [thing] + arr[..i] + arr[i+1..];  // LRU behavior
      arr := a;
      Contents := set x | x in arr;
      assert Valid'();
    }
  }
}

abstract module AbstractClient {
  import S : AbstractInterface

  method Test() {
    var s := new S.StoreAndRetrieve<real>.Init();
    s.Store(20.3);
    var fn := r => true;
    var r := s.Retrieve(fn);
    print r, "\n";  // 20.3
  }
}

module Client refines AbstractClient {
  import S = abC
  method Main() {
    Test();
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
