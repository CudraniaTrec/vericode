
class Set {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>;
  ghost var elems : set<int>;

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
    nelems := 0;
    ghost {
      Repr := {this,store};
      elems := {};
    }
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
    return i >= 0;
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
    if (f < 0) {
      store[nelems] := v;
      ghost elems := elems + {v};
      nelems := nelems + 1;
    }
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
      invariant (forall y :: y in elems && (forall j :: 0 <= j < i ==> store[j] != y) ==> (exists j :: i <= j < nelems && store[j] == y))
    {
      if (store[i]==x) { return i; }
      i := i + 1;
    }
    return -1;
  }
  method Main()
  {
    var s := new Set(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
      }
    }
  }
}

class PositiveSet {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>;
  ghost var elems : set<int>;

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
    nelems := 0;
    ghost {
      Repr := {this,store};
      elems := {};
    }
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
    return i >= 0;
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
      if (f < 0) {
        store[nelems] := v;
        ghost elems := elems + {v};
        nelems := nelems + 1;
      }
    }
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
      invariant (forall y :: y in elems && (forall j :: 0 <= j < i ==> store[j] != y) ==> (exists j :: i <= j < nelems && store[j] == y))
    {
      if (store[i]==x) { return i; }
      i := i + 1;
    }
    return -1;
  }
  method Main()
  {
    var s := new PositiveSet(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
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
    cbalance := 0;
    sbalance := 0;
    ghost {
      Repr := {this};
    }
  }

  method deposit(amount:int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    cbalance := cbalance + amount;
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
    }
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
    }
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
    }
  }
}

class GrowingSet {
  var store:array<int>;
  var nelems: int;

  ghost var Repr : set<object>;
  ghost var elems : set<int>;

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
    nelems := 0;
    ghost {
      Repr := {this,store};
      elems := {};
    }
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
    return i >= 0;
  }
  // adds a new element to the set if space available

  method add(v:int)
    requires RepInv()
    ensures RepInv()
    modifies Repr
    ensures fresh(Repr - old(Repr))
  {
    var f:int := find(v);
    if (f < 0) {
      if(nelems == store.Length) {
        var tmp := new int[store.Length * 2];
        var i:= 0;
        while i < store.Length
          modifies tmp
          invariant 0 <= i <= store.Length
          invariant (forall j :: 0 <= j < i ==> tmp[j] == store[j])
        {
          tmp[i] := store[i];
          i := i + 1;
        }
        ghost {
          Repr := Repr - {store} + {tmp};
        }
        store := tmp;
      }

      store[nelems] := v;
      ghost elems := elems + {v};
      nelems := nelems + 1;
    }
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
      invariant (forall y :: y in elems && (forall j :: 0 <= j < i ==> store[j] != y) ==> (exists j :: i <= j < nelems && store[j] == y))
    {
      if (store[i]==x) { return i; }
      i := i + 1;
    }
    return -1;
  }
  method Main()
  {
    var s := new GrowingSet(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
      }
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
