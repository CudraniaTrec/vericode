
class Set {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {
    store := new int[n];
    Repr := {this,store};
    elems := {};
    nelems := 0;
    assert RepInv();
    assert fresh(Repr-{this});
  }
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {

    var i := find(v);
    assert RepInv();
    b := i >= 0;
    assert (b <==> v in elems);
    return b;
  }
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this,Repr
    ensures fresh(Repr - old(Repr))
  {
    var f:int := find(v);
    assert RepInv();
    if (f < 0) {
      store[nelems] := v;
      elems := elems + {v};
      nelems := nelems + 1;
      assert RepInv();
    }
    assert RepInv();
    assert fresh(Repr - old(Repr));
  }
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {
    var i:int := 0;
    while (i<nelems)
      invariant 0 <= i <= nelems
      invariant RepInv()
      invariant (forall j :: 0 <= j < i ==> store[j] != x)
      invariant (forall j :: 0 <= j < i ==> store[j] in elems)
      invariant (forall y :: y in elems ==> exists j :: 0 <= j < nelems && store[j] == y)
    {
      if (store[i]==x) { r := i; assert RepInv(); assert r >= 0 ==> x in elems; assert r < 0 ==> x !in elems; return r; }
      i := i + 1;
    }
    r := -1;
    assert RepInv();
    assert r < 0 ==> x !in elems;
    assert r >= 0 ==> x in elems;
    return r;
  }
  method Main()
  {
    var s := new Set(10);
    assert s.RepInv();
    if (s.size() < s.maxSize()) {
      s.add(2);
      assert s.RepInv();
      var b := s.contains(2);
      assert b <==> 2 in s.elems;
      if (s.size() < s.maxSize()) {
        s.add(3);
        assert s.RepInv();
      }
    }
  }
}

class PositiveSet {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
    && (forall x :: x in elems ==> x > 0)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {
    store := new int[n];
    Repr := {this,store};
    elems := {};
    nelems := 0;
    assert RepInv();
    assert fresh(Repr-{this});
  }
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {

    var i := find(v);
    assert RepInv();
    b := i >= 0;
    assert (b <==> v in elems);
    return b;
  }
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this,Repr
    ensures fresh(Repr - old(Repr))
  {
    if(v > 0) {
      var f:int := find(v);
      assert RepInv();
      if (f < 0) {
        store[nelems] := v;
        elems := elems + {v};
        nelems := nelems + 1;
        assert RepInv();
      }
    }
    assert RepInv();
    assert fresh(Repr - old(Repr));
  }
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {
    var i:int := 0;
    while (i<nelems)
      invariant 0 <= i <= nelems
      invariant RepInv()
      invariant (forall j :: 0 <= j < i ==> store[j] != x)
      invariant (forall j :: 0 <= j < i ==> store[j] in elems)
      invariant (forall y :: y in elems ==> exists j :: 0 <= j < nelems && store[j] == y)
      invariant (forall j :: 0 <= j < nelems ==> store[j] > 0)
    {
      if (store[i]==x) { r := i; assert RepInv(); assert r >= 0 ==> x in elems; assert r < 0 ==> x !in elems; return r; }
      i := i + 1;
    }
    r := -1;
    assert RepInv();
    assert r < 0 ==> x !in elems;
    assert r >= 0 ==> x in elems;
    return r;
  }
  method Main()
  {
    var s := new PositiveSet(10);
    assert s.RepInv();
    if (s.size() < s.maxSize()) {
      s.add(2);
      assert s.RepInv();
      var b := s.contains(2);
      assert b <==> 2 in s.elems;
      if (s.size() < s.maxSize()) {
        s.add(3);
        assert s.RepInv();
      }
    }
  }
}

class SavingsAccount {

  var cbalance: int;
  var sbalance: int;

  ghost var Repr:set<object>;

  ghost predicate RepInv()
    reads this,Repr
  {
    this in Repr
    && cbalance >= -sbalance/2
  }

  ghost predicate PositiveChecking()
    reads this,Repr
  {
    cbalance >= 0
  }

  constructor()
    ensures fresh(Repr-{this})
    ensures RepInv()
  {
    Repr := {this};
    cbalance := 0;
    sbalance := 0;
    assert RepInv();
    assert fresh(Repr-{this});
  }

  method deposit(amount:int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    cbalance := cbalance + amount;
    assert RepInv();
  }

  method withdraw(amount:int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    if(cbalance-amount >= -sbalance/2)
    {
      cbalance := cbalance - amount;
      assert RepInv();
    }
    assert RepInv();
  }

  method save(amount: int)
    requires amount > 0
    requires PositiveChecking()
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    if(cbalance >= 0)
    {
      sbalance := sbalance + amount;
      assert RepInv();
    }
    assert RepInv();
  }

  method rescue(amount: int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {

    if(cbalance >= -(sbalance-amount)/2)
    {
      sbalance := sbalance - amount;
      assert RepInv();
    }
    assert RepInv();
  }
}

class GrowingSet {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>
  ghost var elems : set<int>


  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
  }
  // the construction operation
  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
  {
    store := new int[n];
    Repr := {this,store};
    elems := {};
    nelems := 0;
    assert RepInv();
    assert fresh(Repr-{this});
  }
  // returns the number of elements in the set
  function size():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }
  // returns the maximum number of elements in the set
  function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }
  // checks if the element given is in the set
  method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {

    var i := find(v);
    assert RepInv();
    b := i >= 0;
    assert (b <==> v in elems);
    return b;
  }
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    ensures RepInv()
    modifies Repr
    ensures fresh(Repr - old(Repr))
  {
    var f:int := find(v);
    assert RepInv();
    if (f < 0) {
      if(nelems == store.Length) {
        var tmp := new int[store.Length * 2];
        var i:= 0;
        while i < store.Length
          invariant 0 <= i <= store.Length
          invariant tmp != null && tmp.Length == store.Length * 2
          invariant (forall j :: 0 <= j < i ==> tmp[j] == store[j])
          modifies tmp
        {
          tmp[i] := store[i];
          i := i + 1;
        }
        Repr := Repr - {store} + {tmp};
        store := tmp;
        assert store in Repr;
        assert this in Repr;
      }

      store[nelems] := v;
      elems := elems + {v};
      nelems := nelems + 1;
      assert RepInv();

    }
    assert RepInv();
    assert fresh(Repr - old(Repr));
  }
  
  // private method that should not be in the
  method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >=0 ==> x in elems;
  {
    var i:int := 0;
    while (i<nelems)
      invariant 0 <= i <= nelems
      invariant RepInv()
      invariant (forall j :: 0 <= j < i ==> store[j] != x)
      invariant (forall j :: 0 <= j < i ==> store[j] in elems)
      invariant (forall y :: y in elems ==> exists j :: 0 <= j < nelems && store[j] == y)
    {
      if (store[i]==x) { r := i; assert RepInv(); assert r >= 0 ==> x in elems; assert r < 0 ==> x !in elems; return r; }
      i := i + 1;
    }
    r := -1;
    assert RepInv();
    assert r < 0 ==> x !in elems;
    assert r >= 0 ==> x in elems;
    return r;
  }
  method Main()
  {
    var s := new GrowingSet(10);
    assert s.RepInv();
    if (s.size() < s.maxSize()) {
      s.add(2);
      assert s.RepInv();
      var b := s.contains(2);
      assert b <==> 2 in s.elems;
      if (s.size() < s.maxSize()) {
        s.add(3);
        assert s.RepInv();
      }
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
