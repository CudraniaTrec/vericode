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
  {
    if n < 2
    then 0
    else Log2Floor(n / 2) + 1
  }

  lemma Log2FloorDef(n: nat)
    requires n >= 1
    ensures Log2Floor(2 * n) == Log2Floor(n) + 1
  {
    // Strongest annotation: direct calculation
    assert 2 * n >= 2;
    assert (2 * n) / 2 == n;
    assert Log2Floor(2 * n) == Log2Floor((2 * n) / 2) + 1;
    assert Log2Floor((2 * n) / 2) == Log2Floor(n);
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
    // Strongest annotation: direct application of equality
    assert x == y;
    assert f(x) == f(y);
  }

  lemma DivisionSubstituteAlternativeReal(x: real, a: real, b: real)
    requires a == b
    requires x != 0.0
    ensures a / x == b / x
  {
    assert a == b;
    assert a / x == b / x;
  }

  lemma DivModAddDenominator(n: nat, m: nat)
    requires m > 0
    ensures (n + m) / m == n / m + 1
    ensures (n + m) % m == n % m
  {
    var zp := (n + m) / m - n / m - 1;
    // Strongest annotation: show (n + m) / m == n / m + 1 and (n + m) % m == n % m
    assert (n + m) / m == n / m + 1;
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
    if a == 0 {
      // Strongest annotation: n == b, so n / m == 0, n % m == b
      assert n == b;
      assert n / m == 0;
      assert n % m == b;
    } else {
      // Strongest annotation: n == a * m + b, a > 0
      assert n / m == a;
      assert n % m == b;
    }
  }

  lemma DivModAddMultiple(a: nat, b: nat, c: nat)
    requires a > 0
    ensures (c * a + b) / a == c + b / a
    ensures (c * a + b) % a == b % a
  {
    calc {
      a * c + b;
    ==
      a * c + (a * (b / a) + b % a);
    ==
      a * (c + b / a) + b % a;
    }
    DivModIsUnique(a * c + b, a, c + b / a, b % a);
    assert (c * a + b) / a == c + b / a;
    assert (c * a + b) % a == b % a;
  }

  lemma DivisionByTwo(x: real)
    ensures 0.5 * x == x / 2.0
  {
    // Strongest annotation: 0.5 == 1/2
    assert 0.5 * x == (1.0 / 2.0) * x;
    assert (1.0 / 2.0) * x == x / 2.0;
  }

  lemma PowerGreater0(base: nat, exponent: nat)
    requires base >= 1
    ensures Power(base, exponent) >= 1
  {
    // Strongest annotation: induction on exponent
    if exponent == 0 {
      assert Power(base, 0) == 1;
    } else if exponent == 1 {
      assert Power(base, 1) == base;
      assert base >= 1;
    } else {
      assert Power(base, exponent) == base * Power(base, exponent - 1);
      PowerGreater0(base, exponent - 1);
      assert Power(base, exponent - 1) >= 1;
      assert base * Power(base, exponent - 1) >= 1;
    }
  }

  lemma Power2OfLog2Floor(n: nat)
    requires n >= 1
    ensures Power(2, Log2Floor(n)) <= n < Power(2, Log2Floor(n) + 1)
  {
    // Strongest annotation: induction on n
    if n < 2 {
      assert Log2Floor(n) == 0;
      assert Power(2, 0) == 1;
      assert 1 <= n < 2;
      assert Power(2, 1) == 2;
    } else {
      assert n >= 2;
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
    assert n < Power(2, Log2Floor(2 * n));
  }

  lemma MulMonotonic(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    ensures a * b <= c * d
  {
    calc {
      a * b;
    <=
      c * b;
    <=
      c * d;
    }
    assert a * b <= c * d;
  }

  lemma MulMonotonicStrictRhs(b: nat, c: nat, d: nat)
    requires b < d
    requires c > 0
    ensures c * b < c * d
  {
    // Strongest annotation: c > 0, b < d
    assert c * b < c * d;
  }

  lemma MulMonotonicStrict(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    requires (a != c && d > 0) || (b != d && c > 0)
    ensures a * b < c * d
  {
    if a != c && d > 0 {
      calc {
        a * b;
      <= { MulMonotonic(a, b, a, d); }
        a * d;
      <
        c * d;
      }
      assert a * b < c * d;
    }
    if b != d && c > 0 {
      calc {
        a * b;
      <=
        c * b;
      < { MulMonotonicStrictRhs(b, c, d); }
        c * d;
      }
      assert a * b < c * d;
    }
  }

  lemma AdditionOfFractions(x: real, y: real, z: real)
    requires z != 0.0
    ensures (x / z) + (y / z) == (x + y) / z
  {
    // Strongest annotation: distributivity of division
    assert (x / z) + (y / z) == (x + y) / z;
  }

  lemma DivSubstituteDividend(x: real, y: real, z: real)
    requires y != 0.0
    requires x == z
    ensures x / y == z / y
  {
    assert x == z;
    assert x / y == z / y;
  }

  lemma DivSubstituteDivisor(x: real, y: real, z: real)
    requires y != 0.0
    requires y == z
    ensures x / y == x / z
  {
    assert y == z;
    assert x / y == x / z;
  }

  lemma DivDivToDivMul(x: real, y: real, z: real)
    requires y != 0.0
    requires z != 0.0
    ensures (x / y) / z == x / (y * z)
  {
    assert (x / y) / z == x / (y * z);
  }

  lemma NatMulNatToReal(x: nat, y: nat)
    ensures (x * y) as real == (x as real) * (y as real)
  {
    assert (x * y) as real == (x as real) * (y as real);
  }

  lemma SimplifyFractions(x: real, y: real, z: real)
    requires z != 0.0
    requires y != 0.0
    ensures (x / z) / (y / z) == x / y
  {
    // Strongest annotation: (x / z) / (y / z) == (x / z) * (z / y) == x / y
    assert (x / z) / (y / z) == (x / z) * (z / y);
    assert (x / z) * (z / y) == x / y;
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
    assert (1.0 / Power(2, k) as real) / 2.0 == 1.0 / (Power(2, k + 1) as real);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
