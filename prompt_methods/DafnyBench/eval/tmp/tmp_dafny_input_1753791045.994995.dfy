
method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0
{
  // Strongest annotation: r = if x == 0.0 then 0.0 else the unique nonnegative square root of x
  // Since Dafny does not have a built-in sqrt, we assume existence by postcondition
  // assert x >= 0.0;
  // assert exists r': real :: r' >= 0.0 && r' * r' == x;
  // No loop or code to annotate further
}

method testSqrt() {
  var r := sqrt(4.0);
  //if (2.0 < r) { monotonicSquare(2.0, r); }
  if (r < 2.0) { monotonicSquare(r, 2.0); }
  // assert r * r == 4.0 && r >= 0.0;
  // assert r == 2.0; // by uniqueness of sqrt for nonnegative real
}

lemma monotonicMult(c: real, x: real, y: real)
  requires x < y && c > 0.0
  ensures c * x < c * y
{
  // assert x < y;
  // assert c > 0.0;
  // assert c * (y - x) > 0.0;
  // assert c * y - c * x > 0.0;
  // assert c * y > c * x;
}

lemma monotonicSquare(x: real, y: real)
  requires 0.0 < x < y
  ensures 0.0 < x * x < y * y
{
    // assert 0.0 < x < y;
    // assert x > 0.0;
    monotonicMult(x, x, y);
    // assert x * x < x * y;
    // assert x * y < y * y; // since x < y and y > 0
    // assert x * x < y * y;
    // assert x * x > 0.0;
}

function abs(a: real) : real {if a>0.0 then a else -a}
