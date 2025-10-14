
function f():nat
  ensures f() == 0
{                  // no problem for methods
  var x := 0;      // no problem without this
  assert x == 0;
  0
}

function abs(a: real) : real {if a>0.0 then a else -a}
