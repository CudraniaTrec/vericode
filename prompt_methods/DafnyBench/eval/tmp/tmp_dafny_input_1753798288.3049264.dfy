
class A {
  var z1: array<nat>
  var z2: array<nat>

  method mm()
    requires z1.Length > 10 && z1[0] == 7
    requires z2.Length > 10 && z2[0] == 17
    modifies z2
  {
    var a: array<nat> := z1;
    a := z2;
    // Strongest assertions about a and z2 at this point:
    assert a == z2;
    assert z2.Length > 10 && z2[0] == 17;
    z2[0] := 27;
    // After assignment:
    assert z2[0] == 27;
    assert a[0] == 27;
    // z2; in pre-state z2[0] == 17
    // z2; z2[0] is currently 27
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
