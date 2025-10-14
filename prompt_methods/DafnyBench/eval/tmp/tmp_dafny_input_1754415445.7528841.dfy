
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
      // Cannot assign to Contents (ghost) in refinement, but Valid' ensures Contents == set x | x in arr
      assert Valid'();
    }
    method Retrieve...
    {
      var j := 0;
      // Strongest possible invariant:
      // - 0 <= j <= |arr|
      // - forall k :: 0 <= k < j ==> !matchCriterion(arr[k])
      // - exists k :: j <= k < |arr| && matchCriterion(arr[k])
      // - Contents == set x | x in arr
      while (j < |arr|)
        invariant 0 <= j <= |arr|
        invariant forall k :: 0 <= k < j ==> !matchCriterion(arr[k])
        invariant exists k :: j <= k < |arr| && matchCriterion(arr[k])
        invariant Valid'()
      {
        if matchCriterion(arr[j]) {
          break;
        }
        j := j + 1;
      }
      assert j < |arr|; // because precondition guarantees existence
      var k := arr[j];
      // Cannot assign to thing; must use a local and return it via the refinement
      // But refinement can't assign to parent method's return, so use a local
      var tmpThing := k;
      assert tmpThing in Contents && matchCriterion(tmpThing);
      assert Contents == old(Contents);
      var a: seq<Thing> :| assume Contents == set x | x in a;
      arr := a;
      assert Valid'();
      // refinement can't assign to thing, but parent assigns thing := k, so we're consistent
    }
  }
}

module abC refines B { // TODO module C causes Go to fail
  class StoreAndRetrieve<Thing(==)> ... {
    method Retrieve...
    {
      var j := 0;
      while (j < |arr|)
        invariant 0 <= j <= |arr|
        invariant forall k :: 0 <= k < j ==> !matchCriterion(arr[k])
        invariant exists k :: j <= k < |arr| && matchCriterion(arr[k])
        invariant Valid'()
      {
        if matchCriterion(arr[j]) {
          break;
        }
        j := j + 1;
      }
      assert j < |arr|;
      var k := arr[j];
      var tmpThing := k;
      assert tmpThing in Contents && matchCriterion(tmpThing);
      assert Contents == old(Contents);
      var a := [tmpThing] + arr[..j] + arr[j+1..];  // LRU behavior
      arr := a;
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
