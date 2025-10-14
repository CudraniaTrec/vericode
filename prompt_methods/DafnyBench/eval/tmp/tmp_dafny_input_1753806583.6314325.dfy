class Set {
  var store: array<int>;
  var nelems: int;

  ghost var Repr: set<object>;
  ghost var elems: set<int>;

  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
  }

  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr - {this})
  {
    store := new int[n];
    nelems := 0;
    ghost Repr := {this, store};
    ghost elems := {};
  }

  function size(): int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }

  function maxSize(): int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }

  method contains(v: int) returns (b: bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {
    var i := find(v);
    b := i >= 0;
  }

  method add(v: int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this, Repr
    ensures fresh(Repr - old(Repr))
  {
    var f: int := find(v);
    if (f < 0) {
      store[nelems] := v;
      ghost elems := elems + {v};
      nelems := nelems + 1;
    }
  }

  method find(x: int) returns (r: int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >= 0 ==> x in elems;
  {
    var i: int := 0;
    while (i < nelems)
      invariant 0 <= i <= nelems
      invariant RepInv()
      invariant (forall j :: 0 <= j < i ==> store[j] != x)
      invariant (forall j :: 0 <= j < i ==> store[j] in elems)
      invariant (forall y :: y in elems ==> exists j :: 0 <= j < nelems && store[j] == y)
    {
      if (store[i] == x) { r := i; return r; }
      i := i + 1;
    }
    r := -1;
    return r;
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
  var store: array<int>;
  var nelems: int;

  ghost var Repr: set<object>;
  ghost var elems: set<int>;

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

  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr - {this})
  {
    store := new int[n];
    nelems := 0;
    ghost Repr := {this, store};
    ghost elems := {};
  }

  function size(): int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }

  function maxSize(): int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }

  method contains(v: int) returns (b: bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {
    var i := find(v);
    b := i >= 0;
  }

  method add(v: int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies this, Repr
    ensures fresh(Repr - old(Repr))
  {
    if (v > 0) {
      var f: int := find(v);
      if (f < 0) {
        store[nelems] := v;
        ghost elems := elems + {v};
        nelems := nelems + 1;
      }
    }
  }

  method find(x: int) returns (r: int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >= 0 ==> x in elems;
  {
    var i: int := 0;
    while (i < nelems)
      invariant 0 <= i <= nelems
      invariant RepInv()
      invariant (forall j :: 0 <= j < i ==> store[j] != x)
      invariant (forall j :: 0 <= j < i ==> store[j] in elems)
      invariant (forall y :: y in elems ==> exists j :: 0 <= j < nelems && store[j] == y)
      invariant (forall j :: 0 <= j < nelems ==> store[j] > 0)
    {
      if (store[i] == x) { r := i; return r; }
      i := i + 1;
    }
    r := -1;
    return r;
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

  ghost var Repr: set<object>;

  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr
    && cbalance >= -sbalance/2
  }

  ghost predicate PositiveChecking()
    reads this, Repr
  {
    cbalance >= 0
  }

  constructor()
    ensures fresh(Repr - {this})
    ensures RepInv()
  {
    cbalance := 0;
    sbalance := 0;
    ghost Repr := {this};
  }

  method deposit(amount: int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    cbalance := cbalance + amount;
  }

  method withdraw(amount: int)
    requires amount > 0
    requires RepInv()
    ensures RepInv()
    modifies Repr
  {
    if (cbalance - amount >= -sbalance/2)
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
    if (cbalance >= 0)
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
    if (cbalance >= -(sbalance - amount)/2)
    {
      sbalance := sbalance - amount;
    }
  }
}

class GrowingSet {
  var store: array<int>;
  var nelems: int;

  ghost var Repr: set<object>;
  ghost var elems: set<int>;

  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && store in Repr &&
    0 < store.Length
    && 0 <= nelems <= store.Length
    && (forall i :: 0 <= i < nelems ==> store[i] in elems)
    && (forall x :: x in elems ==> exists i :: 0 <= i < nelems && store[i] == x)
  }

  constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr - {this})
  {
    store := new int[n];
    nelems := 0;
    ghost Repr := {this, store};
    ghost elems := {};
  }

  function size(): int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { nelems }

  function maxSize(): int
    requires RepInv()
    ensures RepInv()
    reads Repr
  { store.Length }

  method contains(v: int) returns (b: bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in elems
  {
    var i := find(v);
    b := i >= 0;
  }

  method add(v: int)
    requires RepInv()
    ensures RepInv()
    modifies Repr
    ensures fresh(Repr - old(Repr))
  {
    var f: int := find(v);
    if (f < 0) {
      if (nelems == store.Length) {
        var tmp := new int[store.Length * 2];
        var i := 0;
        while i < store.Length
          invariant 0 <= i <= store.Length
          invariant tmp.Length == store.Length * 2
          invariant (forall j :: 0 <= j < i ==> tmp[j] == store[j])
          modifies tmp
        {
          tmp[i] := store[i];
          i := i + 1;
        }
        ghost Repr := Repr - {store} + {tmp};
        store := tmp;
      }
      store[nelems] := v;
      ghost elems := elems + {v};
      nelems := nelems + 1;
    }
  }

  method find(x: int) returns (r: int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in elems
    ensures r >= 0 ==> x in elems;
  {
    var i: int := 0;
    while (i < nelems)
      invariant 0 <= i <= nelems
      invariant RepInv()
      invariant (forall j :: 0 <= j < i ==> store[j] != x)
      invariant (forall j :: 0 <= j < i ==> store[j] in elems)
      invariant (forall y :: y in elems ==> exists j :: 0 <= j < nelems && store[j] == y)
    {
      if (store[i] == x) { r := i; return r; }
      i := i + 1;
    }
    r := -1;
    return r;
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
