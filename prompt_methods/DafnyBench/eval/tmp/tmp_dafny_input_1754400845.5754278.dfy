
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
      ensures a == x + b
      ensures c == 3.14
      ensures b == 17
      ensures a >= 17
      ensures c >= 0.0
    {
      this.a := x;
      c := 3.14;
      new;
      a := a + b;
      assert a == x + b;
      assert c == 3.14;
      assert b == 17;
      assert a >= 17;
      assert c >= 0.0;
    }

    constructor (z: real)
      ensures c <= 2.0 * z
      ensures a == 50
      ensures c == 2.0 * z
      ensures b == 17
      ensures a >= 10
    {
      a, c := 50, 2.0 * z;
      new;
      assert c == 2.0 * z;
      assert c <= 2.0 * z;
      assert a == 50;
      assert b == 17;
      assert a >= 10;
    }

    constructor Make()
      ensures 10 <= a
      ensures a == b
      ensures b == 17
    {
      new;
      a := a + b;
      assert a == b;
      assert 10 <= a;
      assert b == 17;
    }

    constructor Create()
      ensures 30 <= a
      ensures a == 2*b
      ensures b == 17
    {
      new;
      a := a + 2*b;
      assert a == 2 * b;
      assert 30 <= a;
      assert b == 17;
    }
  }
}

module M1 refines M0 {
  class MyClass {
    const d := 'D';
    var e: char;

    constructor Init(x: nat)
      ensures a == x + b
      ensures c == 3.14
      ensures b == 17
      ensures a >= 17
      ensures c >= 0.0
      ensures e == 'x'
      ensures d == 'D'
    {
      e := 'e';
      new;
      e := 'x';
      assert e == 'x';
      assert d == 'D';
      assert a == x + b;
      assert c == 3.14;
      assert b == 17;
      assert a >= 17;
      assert c >= 0.0;
    }

    constructor (z: real)
      ensures c <= 2.0 * z
      ensures a == 50
      ensures c == 2.0 * z
      ensures b == 17
      ensures a >= 10
      ensures e == 'y'
      ensures d == 'D'
    {
      e := 'y';
      new;
      assert e == 'y';
      assert d == 'D';
      assert c == 2.0 * z;
      assert c <= 2.0 * z;
      assert a == 50;
      assert b == 17;
      assert a >= 10;
    }

    constructor Make()
      ensures 10 <= a
      ensures a == b
      ensures b == 17
      ensures e == 'z'
      ensures d == 'D'
    {
      new;
      e := 'z';
      assert e == 'z';
      assert d == 'D';
      assert a == b;
      assert 10 <= a;
      assert b == 17;
    }

    constructor Create()
      ensures 30 <= a
      ensures a == 2*b
      ensures b == 17
      ensures e == 'w'
      ensures d == 'D'
    {
      e := 'w';
      assert e == 'w';
      assert d == 'D';
      assert a == 2 * b;
      assert 30 <= a;
      assert b == 17;
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
      ensures Repr == {this}
    {
      Repr := {this};  // regression test: this should pass, but once upon a time didn't
      assert Repr == {this};
    }

    constructor Init'()
      ensures Rapr == {this}
    {
      Rapr := {this};
      assert Rapr == {this};
    }

    constructor Create()
      ensures S == {this}
    {
      S := {this};  // regression test: this should pass, but once upon a time didn't
      assert S == {this};
    }

    constructor Create'()
      ensures T == {this}
    {
      T := {this};
      assert T == {this};
    }

    constructor Two()
      ensures T == {this} || T == {this: object?}
      ensures S == {this} || S == {this: object}
      ensures Repr == {this} || Repr == {this: LinkedList<T>}
      ensures Rapr == {this} || Rapr == {this: LinkedList?<T>}
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
      assert T == {o} || T == {ll};
      assert S == {o} || S == {ll};
      assert Repr == {ll};
      assert Rapr == {ll};
    }

    method Mutate()
      modifies this
      ensures Repr == {this}
      ensures Rapr == {this}
      ensures S == {this}
      ensures T == {this}
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
      ensures y == 0
    {
      b := false;
      assert b == false;
      assert y == 0;
    }
    constructor Make1()
      ensures b == true
      ensures y == 0
    {
      b := true;
      assert b == true;
      assert y == 0;
    }
    constructor Make2()
      ensures b == false
      ensures y == 0
    {
      b := false;
      new;  // this sets "alloc" to "true", and the verifier previously was not
            // able to distinguish the internal field "alloc" from other boolean
            // fields
      assert b == false;
      assert y == 0;
    }
    constructor Make3()
      ensures b == false && y == 65
    {
      b := false;
      y := 65;
      new;
      assert b == false;
      assert y == 65;
    }
    constructor Make4(bb: bool, yy: int)
      ensures b == bb && y == yy
    {
      b, y := bb, yy;
      assert b == bb;
      assert y == yy;
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
