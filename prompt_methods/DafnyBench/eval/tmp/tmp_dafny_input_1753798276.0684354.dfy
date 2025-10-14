
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
     // At entry: a.value == 11
     assert a.value == 11;

     label L:
     a.value := 12;
     assert a.value == 12;

     label M:
     var oldA := a;
     a := new A(); // Line X
     assert oldA.value == 12; // value of previous a before reassignment
     assert a.value == 10;    // value of new a after construction

     label N:
     a.value := 20;
     assert a.value == 20;

     label P:
     // At this point:
     // - oldA.value == 12 (the object referenced by a before Line X)
     // - a.value == 20 (the new object)
     // - a != oldA
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
