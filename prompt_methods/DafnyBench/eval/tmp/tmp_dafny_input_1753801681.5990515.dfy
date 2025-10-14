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
  // Induction on x
  if x == 0 {
    assert F(0, y) == 0;
    assert 13 * 0 == 0;
  } else {
    if y != 0 {
      AboutF(x, y - 1);
      assert F(x, y) == F(x, y - 1);
      assert F(x, y) == 13 * x;
    } else {
      AboutF(x - 1, 60);
      assert F(x, 0) == F(x - 1, 60) + 13;
      assert F(x, 0) == 13 * (x - 1) + 13;
      assert F(x, 0) == 13 * x;
    }
  }
}

function G(x: nat, ghost y: nat): nat
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
  // Induction on x
  if x == 0 {
    assert G(0, y) == 0;
    assert 13 * 0 == 0;
  } else {
    if y != 0 {
      AboutG(x, y - 1);
      assert G(x, y) == G(x, y - 1);
      assert G(x, y) == 13 * x;
    } else {
      AboutG(x - 1, 60);
      assert G(x, 0) == G(x - 1, 60) + 13;
      assert G(x, 0) == 13 * (x - 1) + 13;
      assert G(x, 0) == 13 * x;
    }
  }
}

function H(x: int, ghost y: nat): int {
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

function J(x: int): int {
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

function K(x: int, ghost y: nat): int {
  K(x, y - 1)
}

method Main() {
  print F(5, 3), "\n"; // 65
  print G(5, 3), "\n"; // 65
  print H(65, 3), "\n"; // 65
  print J(65), "\n"; // 65
}
function abs(a: real) : real {if a>0.0 then a else -a}
