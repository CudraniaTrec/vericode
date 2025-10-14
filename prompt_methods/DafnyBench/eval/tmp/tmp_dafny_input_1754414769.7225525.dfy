// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --function-syntax:4 --relax-definite-assignment

function F(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    F(x, y - 1) // this branch is not compiled (which even makes F auto-accumulator tail recursive)
  else
    F(x - 1, 60) + 13
}

lemma AboutF(x: nat, y: nat)
  ensures F(x, y) == 13 * x
{
  if x == 0 {
    assert F(0, y) == 0;
    assert 13 * 0 == 0;
  } else if y != 0 {
    AboutF(x, y - 1);
    assert F(x, y) == F(x, y - 1);
    assert F(x, y) == 13 * x;
  } else {
    AboutF(x - 1, 60);
    assert F(x, 0) == F(x - 1, 60) + 13;
    assert F(x - 1, 60) == 13 * (x - 1);
    assert F(x, 0) == 13 * (x - 1) + 13;
    assert F(x, 0) == 13 * x;
  }
}

function G(x: nat, ghost y: nat): nat
  ensures G(x, y) == 13 * x
{
  if x == 0 then
    0
  else if y != 0 then
    var z := x + x;
    var a, b, c := 100, if x < z then G(x, y - 1) else G(x, y - 1), 200;
    b // this branch is not compiled (which even makes G auto-accumulator tail recursive)
  else
    G(x - 1, 60) + 13
}

lemma AboutG(x: nat, y: nat)
  ensures G(x, y) == 13 * x
{
  if x == 0 {
    assert G(0, y) == 0;
    assert 13 * 0 == 0;
  } else if y != 0 {
    AboutG(x, y - 1);
    assert G(x, y) == G(x, y - 1);
    assert G(x, y) == 13 * x;
  } else {
    AboutG(x - 1, 60);
    assert G(x, 0) == G(x - 1, 60) + 13;
    assert G(x - 1, 60) == 13 * (x - 1);
    assert G(x, 0) == 13 * (x - 1) + 13;
    assert G(x, 0) == 13 * x;
  }
}

// Ostensibly, the following function is tail recursive. But the ghost-ITE optimization
// removes the tail call. This test ensures that the unused setup for the tail optimization
// does not cause problems.
function H(x: int, ghost y: nat): int
  ensures H(x, y) == x
{
  if y == 0 then
    x
  else
    H(x, y - 1)
}

lemma AboutH(x: int, y: nat)
  ensures H(x, y) == x
{
  if y == 0 {
    assert H(x, 0) == x;
  } else {
    AboutH(x, y - 1);
    assert H(x, y) == H(x, y - 1);
    assert H(x, y) == x;
  }
}

// Like function H, function J looks like it's tail recursive. The compiler probably will
// emit the tail-call label, even though the tail-call is never taken.
function J(x: int): int
  ensures J(x) == x
{
  if true then
    x
  else
    J(x)
}

lemma AboutJ(x: int)
  ensures J(x) == x
{
  assert J(x) == x;
}

// The following function would never verify, and its execution wouldn't terminate.
// Nevertheless, we'll test here that it compiles into legal target code.
function K(x: int, ghost y: nat): int
  decreases y
{
  if y == 0 then
    x
  else
    K(x, y - 1)
}

lemma AboutK(x: int, y: nat)
  ensures K(x, y) == x
{
  if y == 0 {
    assert K(x, 0) == x;
  } else {
    AboutK(x, y - 1);
    assert K(x, y) == K(x, y - 1);
    assert K(x, y) == x;
  }
}

method Main() {
  print F(5, 3), "\n"; // 65
  print G(5, 3), "\n"; // 65
  print H(65, 3), "\n"; // 65
  print J(65), "\n"; // 65
}

function abs(a: real) : real {if a>0.0 then a else -a}
