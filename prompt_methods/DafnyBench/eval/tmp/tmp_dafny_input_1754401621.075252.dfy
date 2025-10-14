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
    // strongest annotation: for b > 0, (a + b) / b == a / b + 1 and (a + b) % b == a % b
    if b > 0 {
      assert ((a + b) / b == a / b + 1) && ((a + b) % b == a % b);
    }
    // for b < 0, similar but negative divisors, not relevant for our other lemmas
  }

  lemma DivModSub1(a: int, b: int)
    requires b != 0
    ensures (a - b) % b == a % b
    ensures (a - b) / b == a / b - 1
  {
    if b > 0 {
      // strongest annotation: for b > 0, (a - b) / b == a / b - 1 and (a - b) % b == a % b
      assert ((a - b) / b == a / b - 1) && ((a - b) % b == a % b);
    }
    // for b < 0, similar but negative divisors, not relevant for our other lemmas
  }

  lemma ModEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a % b == ModSub(a, b)
  {
    reveal ModSub();
    if a < b {
      assert ModSub(a, b) == a;
      assert a % b == a;
    } else {
      assert 0 <= a - b && 0 < b;
      ModEq(a - b, b);
      assert ModSub(a, b) == ModSub(a - b, b);
      assert a % b == (a - b) % b;
      assert a % b == ModSub(a, b);
    }
  }

  lemma DivEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a / b == DivSub(a, b)
  {
    reveal DivSub();
    if a < b {
      assert DivSub(a, b) == 0;
      assert a / b == 0;
    } else {
      assert 0 <= a - b && 0 < b;
      DivEq(a - b, b);
      assert DivSub(a, b) == 1 + DivSub(a - b, b);
      assert a / b == 1 + (a - b) / b;
      assert a / b == DivSub(a, b);
    }
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
      assert ModSub(a, b) == r;
      assert DivSub(a, b) == 0;
      assert DivSub(a, b) == q;
    } else {
      assert a - b == (q - 1) * b + r;
      assert 0 <= a - b && 0 < b;
      assert 0 <= q - 1;
      assert 0 <= r < b;
      DivModSpec'(a - b, b, q - 1, r);
      assert ModSub(a, b) == ModSub(a - b, b);
      assert ModSub(a, b) == r;
      assert DivSub(a, b) == 1 + DivSub(a - b, b);
      assert DivSub(a, b) == q;
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
    assert a % b == r;
    assert a / b == q;
  }

  lemma DivMul(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a * b / b == a
  {
    DivModSpec(a * b, b, a, 0);
    assert (a * b) / b == a;
  }

  lemma DivModMulAdd(a: int, b: int, c: int)
    requires 0 <= a && 0 <= c < b && 0 < b
    ensures (a * b + c) / b == a
    ensures (a * b + c) % b == c
  {
    DivModSpec(a * b + c, b, a, c);
    assert (a * b + c) / b == a;
    assert (a * b + c) % b == c;
  }

}
function abs(a: real) : real {if a>0.0 then a else -a}
