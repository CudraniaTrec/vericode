
// RUN: %dafny /compile:3 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A(0)> {
  var val: A
}

method Nice(n: int) returns (k: int)
  requires n >= 0
  ensures k == n
{
  var f : int -> int := x => x;
  var i := new Ref<int>;
  i.val := 0;
  // Invariant: i.val in 0..n, f(x) == x + i.val, i.val <= n
  while i.val < n
    invariant 0 <= i.val <= n
    invariant forall x :: f(x) == x + i.val
  {
    i.val := i.val + 1;
    f := x => f(x) + 1;
    assert forall x :: f(x) == x + i.val;
  }
  assert f(0) == i.val;
  return f(0);
}

method OneShot(n: int) returns (k: int)
  requires n >= 0
  ensures k == n
{
  var f : int -> int := x => x;
  var i := 0;
  // Invariant: i in 0..n, f(x) == x + i
  while i < n
    invariant 0 <= i <= n
    invariant forall x :: f(x) == x + i
  {
    i := i + 1;
    f := x requires f.requires(x) reads f.reads(x) => f(x) + 1;
    assert forall x :: f(x) == x + i;
  }
  k := f(0);
  assert k == n;
}

method HeapQuant(n: int) returns (k: int)
  requires n >= 0
  ensures k == n
{
  var f : int -> int := x => x;
  var i := new Ref;
  ghost var r := 0;
  i.val := 0;
  // Invariant: i.val in 0..n, r == i.val, f(x) == x + i.val
  while i.val < n
    invariant 0 <= i.val <= n
    invariant r == i.val
    invariant forall x :: f(x) == x + i.val
  {
    i.val, r := i.val + 1, r + 1;
    f := x => f(x) + 1;
    assert r == i.val;
    assert forall x :: f(x) == x + i.val;
  }
  k := f(0);
  assert k == n;
}

method Main() {
  var k0 := Nice(22);
  var k1 := OneShot(22);
  var k2 := HeapQuant(22);
  print k0, " ", k1, " ", k2, "\n";
}

function abs(a: real) : real {if a>0.0 then a else -a}
