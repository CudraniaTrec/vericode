/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Helper {
  /************
   Definitions
  ************/

  function Power(b: nat, n: nat): (p: nat)
    ensures b > 0 ==> p > 0
  {
    match n
    case 0 => 1
    case 1 => b
    case _ => b * Power(b, n - 1)
  }

  function Log2Floor(n: nat): nat
    requires n >= 1
    decreases n
  {
    if n < 2
    then 0
    else Log2Floor(n / 2) + 1
  }

  lemma Log2FloorDef(n: nat)
    requires n >= 1
    ensures Log2Floor(2 * n) == Log2Floor(n) + 1
  {
    // Strongest annotation: by definition of Log2Floor
    if n < 2 {
      assert n == 1;
      assert 2 * n == 2;
      assert Log2Floor(2) == 1;
      assert Log2Floor(1) == 0;
      assert Log2Floor(2 * n) == Log2Floor(n) + 1;
    } else {
      assert (2 * n) / 2 == n;
      assert Log2Floor(2 * n) == Log2Floor((2 * n) / 2) + 1;
      assert Log2Floor((2 * n) / 2) == Log2Floor(n);
      assert Log2Floor(2 * n) == Log2Floor(n) + 1;
    }
  }

  function boolToNat(b: bool): nat {
    if b then 1 else 0
  }

  /*******
   Lemmas
  *******/

  lemma Congruence<T, U>(x: T, y: T, f: T -> U)
    requires x == y
    ensures f(x) == f(y)
  {
    // Direct consequence of equality
  }

  lemma DivisionSubstituteAlternativeReal(x: real, a: real, b: real)
    requires a == b
    requires x != 0.0
    ensures a / x == b / x
  {
    // Direct consequence of equality
  }

  lemma DivModAddDenominator(n: nat, m: nat)
    requires m > 0
    ensures (n + m) / m == n / m + 1
    ensures (n + m) % m == n % m
  {
    // Let q := n / m, r := n % m, so n = q*m + r, 0 <= r < m
    var q := n / m;
    var r := n % m;
    assert n == q * m + r;
    assert 0 <= r < m;
    assert n + m == q * m + (r + m);
    assert (r + m) >= m && (r + m) < 2 * m;
    assert (n + m) / m == (q * m + (r + m)) / m;
    assert (q * m + (r + m)) / m == q + ((r + m) / m);
    assert (r + m) / m == 1;
    assert (n + m) / m == q + 1;
    assert (n + m) / m == n / m + 1;
    assert (n + m) % m == (r + m) % m;
    assert (r + m) % m == r;
    assert (n + m) % m == n % m;
  }

  lemma DivModIsUnique(n: int, m: int, a: int, b: int)
    requires n >= 0
    requires m > 0
    requires 0 <= b < m
    requires n == a * m + b
    ensures a == n / m
    ensures b == n % m
  {
    // By definition of div/mod for n >= 0, m > 0, 0 <= b < m, n = a*m + b
    // n / m = a, n % m = b
  }

  lemma DivModAddMultiple(a: nat, b: nat, c: nat)
    requires a > 0
    ensures (c * a + b) / a == c + b / a
    ensures (c * a + b) % a == b % a
  {
    // Let q := b / a, r := b % a, so b = q*a + r, 0 <= r < a
    var q := b / a;
    var r := b % a;
    assert b == q * a + r;
    assert 0 <= r < a;
    assert c * a + b == c * a + q * a + r == (c + q) * a + r;
    DivModIsUnique(c * a + b, a, c + q, r);
    assert (c * a + b) / a == c + q == c + b / a;
    assert (c * a + b) % a == r == b % a;
  }

  lemma DivisionByTwo(x: real)
    ensures 0.5 * x == x / 2.0
  {
    // 0.5 * x == x / 2.0 by arithmetic
  }

  lemma PowerGreater0(base: nat, exponent: nat)
    requires base >= 1
    ensures Power(base, exponent) >= 1
  {
    // Induction on exponent
    if exponent == 0 {
      assert Power(base, 0) == 1;
    } else if exponent == 1 {
      assert Power(base, 1) == base;
      assert base >= 1;
    } else {
      assert Power(base, exponent) == base * Power(base, exponent - 1);
      PowerGreater0(base, exponent - 1);
      assert Power(base, exponent - 1) >= 1;
      assert base * Power(base, exponent - 1) >= 1 * 1;
      assert Power(base, exponent) >= 1;
    }
  }

  lemma Power2OfLog2Floor(n: nat)
    requires n >= 1
    ensures Power(2, Log2Floor(n)) <= n < Power(2, Log2Floor(n) + 1)
  {
    // Induction on n
    if n < 2 {
      assert n == 1;
      assert Log2Floor(1) == 0;
      assert Power(2, 0) == 1;
      assert 1 <= 1 < 2;
      assert Power(2, Log2Floor(n)) <= n < Power(2, Log2Floor(n) + 1);
    } else {
      var k := Log2Floor(n / 2);
      assert Log2Floor(n) == k + 1;
      Power2OfLog2Floor(n / 2);
      assert Power(2, k) <= n / 2 < Power(2, k + 1);
      assert Power(2, k + 1) == 2 * Power(2, k);
      assert Power(2, k + 1) <= n < Power(2, k + 2);
      assert Power(2, Log2Floor(n)) <= n < Power(2, Log2Floor(n) + 1);
    }
  }

  lemma NLtPower2Log2FloorOf2N(n: nat)
    requires n >= 1
    ensures n < Power(2, Log2Floor(2 * n))
  {
    calc {
      n;
    < { Power2OfLog2Floor(n); }
      Power(2, Log2Floor(n) + 1);
    == { Log2FloorDef(n); }
      Power(2, Log2Floor(2 * n));
    }
  }

  lemma MulMonotonic(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    ensures a * b <= c * d
  {
    // a * b <= a * d <= c * d
    assert a * b <= a * d;
    assert a * d <= c * d;
    assert a * b <= c * d;
  }

  lemma MulMonotonicStrictRhs(b: nat, c: nat, d: nat)
    requires b < d
    requires c > 0
    ensures c * b < c * d
  {
    // c * b < c * d since c > 0 and b < d
  }

  lemma MulMonotonicStrict(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    requires (a != c && d > 0) || (b != d && c > 0)
    ensures a * b < c * d
  {
    if a != c && d > 0 {
      assert a < c;
      assert a * d < c * d;
      assert a * b <= a * d;
      assert a * b < c * d;
    }
    if b != d && c > 0 {
      assert b < d;
      assert c * b < c * d;
      assert a * b <= c * b;
      assert a * b < c * d;
    }
  }

  lemma AdditionOfFractions(x: real, y: real, z: real)
    requires z != 0.0
    ensures (x / z) + (y / z) == (x + y) / z
  {
    // (x / z) + (y / z) == (x + y) / z by algebra
  }

  lemma DivSubstituteDividend(x: real, y: real, z: real)
    requires y != 0.0
    requires x == z
    ensures x / y == z / y
  {
    // Direct consequence of equality
  }

  lemma DivSubstituteDivisor(x: real, y: real, z: real)
    requires y != 0.0
    requires y == z
    ensures x / y == x / z
  {
    // Direct consequence of equality
  }

  lemma DivDivToDivMul(x: real, y: real, z: real)
    requires y != 0.0
    requires z != 0.0
    ensures (x / y) / z == x / (y * z)
  {
    // (x / y) / z == x / (y * z) by algebra
  }

  lemma NatMulNatToReal(x: nat, y: nat)
    ensures (x * y) as real == (x as real) * (y as real)
  {
    // By definition of as real and *
  }

  lemma SimplifyFractions(x: real, y: real, z: real)
    requires z != 0.0
    requires y != 0.0
    ensures (x / z) / (y / z) == x / y
  {
    // ((x / z) / (y / z)) == (x / z) * (z / y) == x / y
  }

  lemma PowerOfTwoLemma(k: nat)
    ensures (1.0 / Power(2, k) as real) / 2.0 == 1.0 / (Power(2, k + 1) as real)
  {
    calc {
      (1.0 / Power(2, k) as real) / 2.0;
    == { DivDivToDivMul(1.0, Power(2, k) as real, 2.0); }
      1.0 / (Power(2, k) as real * 2.0);
    == { NatMulNatToReal(Power(2, k), 2); }
      1.0 / (Power(2, k) * 2) as real;
    ==
      1.0 / (Power(2, k + 1) as real);
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
