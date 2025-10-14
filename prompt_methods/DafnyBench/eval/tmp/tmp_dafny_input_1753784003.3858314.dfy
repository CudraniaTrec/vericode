// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= n;

method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0;
/*Post-Condition*/ ensures z==power(x,y0);
{
  var y := y0;  //This is here for Dafny's sake and immutable inputs...

  z := 1;

  while (y > 0)
    invariant 0 <= y <= y0;
    invariant z == power(x, y0 - y);
    decreases y;
  {
    z := z * x;
    y := y - 1;
  }
  assert y == 0;
  assert z == power(x, y0 - y);
}

function abs(a: real) : real {if a>0.0 then a else -a}
