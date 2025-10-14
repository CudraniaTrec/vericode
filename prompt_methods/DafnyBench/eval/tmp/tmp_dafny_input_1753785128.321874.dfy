// RUN: %dafny /compile:3 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var m := new M0.MyClass.Init(20);
  print m.a, ", ", m.b, ", ", m.c, "\n";
  var r0 := new Regression.A.Make0();
  var r1 := new Regression.A.Make1();
  print r0.b, ", ", r1.b, "\n";
}

module M0 {
  class MyClass {
    var a: nat
    const b := 17
    var c: real

    constructor Init(x: nat)
    {
      a := x;
      c := 3.14;
      new;
      a := a + b;
      assert a == x + b;
      assert c == 3.14;
    }

    constructor (z: real)
      ensures c <= 2.0 * z
    {
      a := 50;
      c := 2.0 * z;
      new;
      assert c == 2.0 * z;
      assert c <= 2.0 * z;
      assert a == 50;
    }

    constructor Make()
      ensures 10 <= a
    {
      new;
      a := a + b;
      assert 10 <= a;
    }

    constructor Create()
      ensures 30 <= a
    {
      new;
      a := a + 2*b;
      assert 30 <= a;
    }
  }
}

module M1 refines M0 {
  class MyClass ... {
    const d := 'D';
    var e: char;

    constructor Init(x: nat)
    {
      e := 'e';
      new;
      e := 'x';
      assert e == 'x';
    }

    constructor (z: real)
      ensures c <= 2.0 * z
    {
      e := 'y';
      new;
      assert e == 'y';
      assert c <= 2.0 * z;
    }

    constructor Make()
      ensures 10 <= a
    {
      new;
      e := 'z';
      assert e == 'z';
      assert 10 <= a;
    }

    constructor Create()
      ensures 30 <= a
    {
      new;
      e := 'w';
      assert e == 'w';
      assert 30 <= a;
    }
  }
}

module TypeOfThis {
  class LinkedList<T(0)> {
    ghost var Repr: set<LinkedList<T>>
    ghost var Rapr: set<LinkedList?<T>>
    ghost var S: set<object>
    ghost var T: set<object?>

    constructor Init()
    {
      Repr := {this};
      // Only field assignment allowed here
    }

    constructor Init'()
    {
      Rapr := {this};
      // Only field assignment allowed here
    }

    constructor Create()
    {
      S := {this};
      // Only field assignment allowed here
    }

    constructor Create'()
    {
      T := {this};
      // Only field assignment allowed here
    }

    constructor Two()
    {
      new;
      var ll: LinkedList? := this;
      var o: object? := this;
      if
      case true =>  T := {o};
      case true =>  S := {o};
      case true =>  Repr := {ll};
      case true =>  Rapr := {ll};
      case true =>  S := {ll};
      case true =>  T := {ll};
      // Only field assignment allowed before new; all assertions must be after new;
    }

    method Mutate()
      modifies this
    {
      Repr := {this};
      Rapr := {this};
      S := {this};
      T := {this};
      assert Repr == {this};
      assert Rapr == {this};
      assert S == {this};
      assert T == {this};
    }
  }
}

module Regression {
  class A {
    var b: bool
    var y: int

    constructor Make0()
      ensures b == false  // regression test: this didn't used to be provable :O
    {
      b := false;
      assert b == false;
    }
    constructor Make1()
      ensures b == true
    {
      b := true;
      assert b == true;
    }
    constructor Make2()
    {
      b := false;
      new;
      assert b == false;
    }
    constructor Make3()
      ensures b == false && y == 65
    {
      b := false;
      y := 65;
      new;
      assert b == false && y == 65;
    }
    constructor Make4(bb: bool, yy: int)
      ensures b == bb && y == yy
    {
      b := bb;
      y := yy;
      assert b == bb && y == yy;
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
