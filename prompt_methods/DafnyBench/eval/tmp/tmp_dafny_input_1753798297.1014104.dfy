
class A {

  var value: int

  method m(i: int)
    requires i == 6
    requires value == 42
    modifies this
  {
    var j: int := 17;
    assert i == 6;
    assert value == 42;
    value := 43;
    assert value == 43;
    label L:
    assert j == 17;
    j := 18;
    assert j == 18;
    value := 44;
    assert value == 44;
    label M:
    // value is this.value; 'this' is the same
    // same reference in current and pre state but the
    // values stored in the heap as its fields are different;
    // '.value' evaluates to 42 in the pre-state, 43 at L,
    // and 44 in the current state
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
