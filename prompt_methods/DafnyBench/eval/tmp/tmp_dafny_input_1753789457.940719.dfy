// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Spec# and Boogie and Chalice:  The program will be
// the same, except that these languages do not check
// for any kind of termination.  Also, in Spec#, there
// is an issue of potential overflows.

// Benchmark1

method Add(x: int, y: int) returns (r: int)
  ensures r == x+y;
{
  r := x;
  if (y < 0) {
    var n := y;
    while (n != 0)
      invariant n <= 0
      invariant n >= y
      invariant r + n == x + y
      decreases -n
    {
      r := r - 1;
      n := n + 1;
      assert n <= 0;
      assert n >= y;
      assert r + n == x + y;
    }
  } else {
    var n := y;
    while (n != 0)
      invariant n >= 0
      invariant n <= y
      invariant r + n == x + y
      decreases n
    {
      r := r + 1;
      n := n - 1;
      assert n >= 0 || n == 0;
      assert n <= y;
      assert r + n == x + y;
    }
  }
}

method Mul(x: int, y: int) returns (r: int)
  ensures r == x*y;
{
  if (x == 0) {
    r := 0;
    assert r == x*y;
  } else if (x < 0) {
    r := Mul(-x, y);
    assert r == (-x)*y;
    r := -r;
    assert r == x*y;
  } else {
    r := Mul(x-1, y);
    assert r == (x-1)*y;
    r := Add(r, y);
    assert r == (x-1)*y + y;
    assert r == x*y;
  }
}

// ---------------------------

method Main() {
  TestAdd(3, 180);
  TestAdd(3, -180);
  TestAdd(0, 1);

  TestMul(3, 180);
  TestMul(3, -180);
  TestMul(180, 3);
  TestMul(-180, 3);
  TestMul(0, 1);
  TestMul(1, 0);
}

method TestAdd(x: int, y: int) {
  print x, " + ", y, " = ";
  var z := Add(x, y);
  print z, "\n";
}

method TestMul(x: int, y: int) {
  print x, " * ", y, " = ";
  var z := Mul(x, y);
  print z, "\n";
}

function abs(a: real) : real {if a>0.0 then a else -a}
