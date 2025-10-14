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
      assert Valid'();
    }
    method Retrieve...
    {
      var idx := 0;
      while (idx < |arr|)
        invariant 0 <= idx <= |arr|
        invariant forall m :: 0 <= m < idx ==> !matchCriterion(arr[m])
        invariant exists m :: idx <= m < |arr| && matchCriterion(arr[m])
        invariant Valid'()
      {
        if matchCriterion(arr[idx]) {
          break;
        }
        idx := idx + 1;
      }
      assert idx < |arr|; // because precondition guarantees existence
      var found := arr[idx];
      var localThing := found;
      assert localThing in Contents && matchCriterion(localThing);
      assert Contents == old(Contents);
      var arrPrime: seq<Thing> :| assume Contents == set x | x in arrPrime;
      arr := arrPrime;
      assert Valid'();
    }
  }
}

module abC refines B { // TODO module C causes Go to fail
  class StoreAndRetrieve<Thing(==)> ... {
    method Retrieve...
    {
      var idx := 0;
      while (idx < |arr|)
        invariant 0 <= idx <= |arr|
        invariant forall m :: 0 <= m < idx ==> !matchCriterion(arr[m])
        invariant exists m :: idx <= m < |arr| && matchCriterion(arr[m])
        invariant Valid'()
      {
        if matchCriterion(arr[idx]) {
          break;
        }
        idx := idx + 1;
      }
      assert idx < |arr|;
      var found := arr[idx];
      var localThing := found;
      assert localThing in Contents && matchCriterion(localThing);
      assert Contents == old(Contents);
      var arrNew := [localThing] + arr[..idx] + arr[idx+1..];  // LRU behavior
      arr := arrNew;
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
