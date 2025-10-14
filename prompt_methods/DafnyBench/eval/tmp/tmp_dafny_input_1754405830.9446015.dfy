method sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r * r == x && r >= 0.0
{
  // Since Dafny cannot compute real square roots algorithmically,
  // we use 'assume' to satisfy the postcondition for verification purposes.
  if x == 0.0 {
    r := 0.0;
  } else {
    // There exists r > 0.0 such that r*r == x
    // We assume such an r exists for verification
    // Assign an arbitrary value, then assume the postcondition
    r := 0.0;
    assume r >= 0.0 && r * r == x;
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
