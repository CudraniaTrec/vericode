// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

abstract module M0 {
  class Counter {
    ghost var N: int
    ghost var Repr: set<object>
    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    constructor Init()
      ensures N == 0
      ensures Valid() && fresh(Repr)
    {
      Repr := {};
      new;
      ghost var repr :| {this} <= repr && fresh(repr - {this});
      N, Repr := 0, repr;
      assume Valid();  // to be verified in refinement module
    }

    method Inc()
      requires Valid()
      modifies Repr
      ensures N == old(N) + 1
      ensures Valid() && fresh(Repr - old(Repr))
    {
      N := N + 1;
      modify Repr - {this};
      assume Valid();  // to be verified in refinement module
    }

    method Get() returns (n: int)
      requires Valid()
      ensures n == N
    {
      n :| assume n == N;
    }
  }
}

module M1 refines M0 {
  class Cell {
    var data: int
    constructor (d: int)
      ensures data == d
    { data := d; }
  }

  class Counter ...
  {
    var c: Cell
    var d: Cell
    ghost predicate Valid() 
      reads this, Repr
    {
      this in Repr &&
      c in Repr &&
      d in Repr &&
      c != d &&
      N == c.data - d.data
    }

    constructor Init() 
      ensures N == 0
      ensures Valid() && fresh(Repr)
    {
      c := new Cell(0);
      d := new Cell(0);
      new;
      ghost var repr := {this, c, d};
      N, Repr := 0, repr;
      assert c != d;
      assert this in Repr && c in Repr && d in Repr;
      assert N == c.data - d.data;
      assert Valid();
    }

    method Inc() 
      requires Valid()
      modifies Repr
      ensures N == old(N) + 1
      ensures Valid() && fresh(Repr - old(Repr))
    {
      N := N + 1;
      modify Repr - {this} {
        c.data := c.data + 1;
        assert N == c.data - d.data;
      }
      assert Valid();
    }

    method Get() returns (n: int)
      requires Valid()
      ensures n == N
    {
      n := c.data - d.data;
      assert n == N;
    }
  }
}

method Main() {
  var mx := new M1.Counter.Init();
  var my := new M1.Counter.Init();
  mx.Inc();
  my.Inc();
  mx.Inc();
  var nx := mx.Get();
  var ny := my.Get();
  print nx, " ", ny, "\n";
}

function abs(a: real) : real {if a>0.0 then a else -a}
