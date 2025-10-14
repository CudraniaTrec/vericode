method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0
{
  // For real numbers, we assume existence of such r.
  // To satisfy the postcondition, we can use 'ghost' assignment.
  // In actual code, this would be implemented numerically, but for verification, we can use 'assume'.
  // (Dafny does not compute real square roots algorithmically.)
  if x == 0.0 {
    r := 0.0;
  } else {
    // There exists r > 0.0 such that r*r == x
    // We "assume" existence for verification
    ghost var rr: real :| rr >= 0.0 && rr * rr == x;
    r := rr;
  }
  assert r >= 0.0;
  assert r * r == x;
}

method testSqrt() {
  var r := sqrt(4.0);
  //if (2.0 < r) { monotonicSquare(2.0, r); }
  if (r < 2.0) { monotonicSquare(r, 2.0); }
}

lemma monotonicMult(c: real, x: real, y: real)
  requires x < y && c > 0.0
  ensures c * x < c * y
{
  assert x < y;
  assert c > 0.0;
  assert c * x < c * y;
}

lemma monotonicSquare(x: real, y: real)
  requires 0.0 < x < y
  ensures 0.0 < x * x < y * y
{
  assert 0.0 < x;
  assert x < y;
  assert x * x < x * y;
  assert x * y < y * y;
  assert x * x < y * y;
  assert x * x > 0.0;
  assert 0.0 < x * x < y * y;
}
function abs(a: real) : real {if a>0.0 then a else -a}
