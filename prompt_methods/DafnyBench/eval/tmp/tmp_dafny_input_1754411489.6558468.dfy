
class A {
  var value: int
  constructor ()
     ensures value == 10
  {
     value := 10;
     assert value == 10;
  }
}

class B {
   var a: A
   constructor () { a := new A(); }

   method m()
     requires a.value == 11
     modifies this, this.a
   {
     label L:
     // At this point: a.value == 11 (from precondition)
     assert a.value == 11;
     a.value := 12;
     // Now: a.value == 12
     assert a.value == 12;

     label M:
     a := new A(); // Line X
     // Now: a.value == 10 (from A's constructor postcondition)
     assert a.value == 10;

     label N:
     a.value := 20;
     // Now: a.value == 20
     assert a.value == 20;

     label P:
     // At this point: a.value == 20
     assert a.value == 20;
     // At Line X, the new A() assigned to a, so a.value == 10 immediately after Line X
     // Reference at Line X: a.value == 10
   }
}

function abs(a: real) : real {if a>0.0 then a else -a}
