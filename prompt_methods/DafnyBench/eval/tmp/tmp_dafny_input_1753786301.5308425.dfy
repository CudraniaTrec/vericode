module DivMod {

  function {:opaque} DivSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {
    if a < b then 0 else 1 + DivSub(a - b, b)
  }

  function {:opaque} ModSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {
    if a < b then a else ModSub(a - b, b)
  }

  lemma DivModAdd1(a: int, b: int)
    requires b != 0
    ensures (a + b) % b == a % b
    ensures (a + b) / b == a / b + 1
  {
    // No code needed, postconditions are true by Dafny's arithmetic.
  }

  lemma DivModSub1(a: int, b: int)
    requires b != 0
    ensures (a - b) % b == a % b
    ensures (a - b) / b == a / b - 1
  {
    // No code needed, postconditions are true by Dafny's arithmetic.
  }

  lemma ModEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a % b == ModSub(a, b)
  {
    reveal ModSub();
    var x := a;
    while x >= b
      invariant 0 <= x <= a
      invariant a % b == x % b
      decreases x
    {
      x := x - b;
    }
    assert x < b;
    assert x == ModSub(a, b);
    assert a % b == x;
  }

  lemma DivEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a / b == DivSub(a, b)
  {
    reveal DivSub();
    var x := a;
    var q := 0;
    while x >= b
      invariant 0 <= x <= a
      invariant 0 <= q <= a / b
      invariant a == x + q * b
      decreases x
    {
      x := x - b;
      q := q + 1;
    }
    assert x < b;
    assert q == DivSub(a, b);
    assert a / b == q;
  }

  lemma DivModSpec'(a: int, b: int, q: int, r: int)
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    ensures ModSub(a, b) == r
    ensures DivSub(a, b) == q
  {
    reveal ModSub();
    reveal DivSub();
    if q == 0 {
      assert a == r;
      assert a < b;
      assert ModSub(a, b) == a;
      assert DivSub(a, b) == 0;
    } else {
      assert a - b == (q - 1) * b + r;
      DivModSpec'(a - b, b, q - 1, r);
      assert ModSub(a, b) == ModSub(a - b, b);
      assert DivSub(a, b) == 1 + DivSub(a - b, b);
    }
  }

  lemma DivModSpec(a: int, b: int, q: int, r: int)
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    ensures a % b == r
    ensures a / b == q
  {
    ModEq(a, b);
    DivEq(a, b);
    DivModSpec'(a, b, q, r);
  }

  lemma DivMul(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a * b / b == a
  {
    DivModSpec(a * b, b, a, 0);
  }

  lemma DivModMulAdd(a: int, b: int, c: int)
    requires 0 <= a && 0 <= c < b && 0 < b
    ensures (a * b + c) / b == a
    ensures (a * b + c) % b == c
  {
    DivModSpec(a * b + c, b, a, c);
  }

}
function abs(a: real) : real {if a>0.0 then a else -a}
