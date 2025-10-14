
// Based on IronFleet's math library.
// I pulled out only the functions we need for the marshalling code,
// and in a few cases rewrote the proof from scratch to avoid pulling in
// a lot of dependencies.

module Math {
  function {:opaque} power2(exp: nat) : nat
      ensures power2(exp) > 0;
  {
      if (exp==0) then
          1
      else
          2*power2(exp-1)
  }

  lemma lemma_2toX()
      ensures power2(8) ==  256;
      ensures power2(16) == 65536;
      ensures power2(19) == 524288;
      ensures power2(24) == 16777216;
      ensures power2(32) == 4294967296;
      ensures power2(60) == 1152921504606846976;
      ensures power2(64) == 18446744073709551616;
  {
    reveal_power2();
    assert power2(8) == 256;
    assert power2(16) == 65536;
    assert power2(19) == 524288;
    assert power2(24) == 16777216;
    assert power2(32) == 4294967296;
    assert power2(60) == 1152921504606846976;
    assert power2(64) == 18446744073709551616;
  }

  lemma lemma_power2_adds(e1:nat, e2:nat)
      ensures power2(e1 + e2) == power2(e1) * power2(e2);
  {
    reveal_power2();
    if (e2 == 0) {
      assert power2(e1 + 0) == power2(e1);
      assert power2(e1) * power2(0) == power2(e1) * 1 == power2(e1);
    } else {
      lemma_power2_adds(e1, e2-1);
      assert power2(e1 + e2) == 2 * power2(e1 + e2 - 1);
      assert power2(e1) * power2(e2) == power2(e1) * (2 * power2(e2 - 1));
      assert power2(e1) * power2(e2) == 2 * (power2(e1) * power2(e2 - 1));
      assert power2(e1 + e2) == power2(e1) * power2(e2);
    }
  }

  lemma lemma_2toX32()
      ensures power2(0) == 0x1;
      ensures power2(1) == 0x2;
      ensures power2(2) == 0x4;
      ensures power2(3) == 0x8;
      ensures power2(4) == 0x10;
      ensures power2(5) == 0x20;
      ensures power2(6) == 0x40;
      ensures power2(7) == 0x80;
      ensures power2(8) == 0x100;
      ensures power2(9) == 0x200;
      ensures power2(10) == 0x400;
      ensures power2(11) == 0x800;
      ensures power2(12) == 0x1000;
      ensures power2(13) == 0x2000;
      ensures power2(14) == 0x4000;
      ensures power2(15) == 0x8000;
      ensures power2(16) == 0x10000;
      ensures power2(17) == 0x20000;
      ensures power2(18) == 0x40000;
      ensures power2(19) == 0x80000;
      ensures power2(20) == 0x100000;
      ensures power2(21) == 0x200000;
      ensures power2(22) == 0x400000;
      ensures power2(23) == 0x800000;
      ensures power2(24) == 0x1000000;
      ensures power2(25) == 0x2000000;
      ensures power2(26) == 0x4000000;
      ensures power2(27) == 0x8000000;
      ensures power2(28) == 0x10000000;
      ensures power2(29) == 0x20000000;
      ensures power2(30) == 0x40000000;
      ensures power2(31) == 0x80000000;
      ensures power2(32) == 0x100000000;
  {
    reveal_power2();
    assert power2(0) == 0x1;
    assert power2(1) == 0x2;
    assert power2(2) == 0x4;
    assert power2(3) == 0x8;
    assert power2(4) == 0x10;
    assert power2(5) == 0x20;
    assert power2(6) == 0x40;
    assert power2(7) == 0x80;
    assert power2(8) == 0x100;
    assert power2(9) == 0x200;
    assert power2(10) == 0x400;
    assert power2(11) == 0x800;
    assert power2(12) == 0x1000;
    assert power2(13) == 0x2000;
    assert power2(14) == 0x4000;
    assert power2(15) == 0x8000;
    assert power2(16) == 0x10000;
    assert power2(17) == 0x20000;
    assert power2(18) == 0x40000;
    assert power2(19) == 0x80000;
    assert power2(20) == 0x100000;
    assert power2(21) == 0x200000;
    assert power2(22) == 0x400000;
    assert power2(23) == 0x800000;
    assert power2(24) == 0x1000000;
    assert power2(25) == 0x2000000;
    assert power2(26) == 0x4000000;
    assert power2(27) == 0x8000000;
    assert power2(28) == 0x10000000;
    assert power2(29) == 0x20000000;
    assert power2(30) == 0x40000000;
    assert power2(31) == 0x80000000;
    assert power2(32) == 0x100000000;
  }

  lemma bounded_mul_eq_0(x: int, m: int)
  requires -m < m*x < m
  ensures x == 0
  {
    // strongest assertion: m != 0
    assert m != 0;
    // m*x < m  ==> x < 1 if m > 0, x > -1 if m < 0
    if (m > 0) {
      assert -m < m*x < m;
      assert -1 < x < 1;
      assert x == 0;
    } else if (m < 0) {
      assert -m < m*x < m;
      assert m < 0;
      assert m*x > -m;
      assert x < 1 && x > -1;
      assert x == 0;
    }
  }

  // This is often used as part of the axiomatic definition of division
  // in a lot of formalizations of mathematics. Oddly, it isn't built-in to dafny
  // and we have to prove it in sort of a roundabout way.
  lemma lemma_div_ind(x: int, d: int)
  requires d > 0
  ensures x / d + 1 == (x + d) / d
  {
        // x / d + 1 == (x + d) / d
        // Let's show (x + d) / d == x / d + 1
        // (x + d) / d = ((x / d) * d + (x % d) + d) / d
        //             = ((x / d) * d + d + (x % d)) / d
        //             = ((x / d) + 1) + (x % d) / d
        // But 0 <= x % d < d, so (x % d) / d == 0
        // So (x + d) / d == (x / d) + 1
        assert 0 <= x % d < d;
        assert (x + d) / d == (x / d) + 1;
        assert x / d + 1 == (x + d) / d;

        // The following lines are for the proof structure in the original code:
        // == (x/d)*d + d
        // == x - (x % d) + d;
        // == (x + d) - ((x + d) % d);
        // == ((x + d) % d) - (x % d);
        // bounded_mul_eq_0((x / d + 1) - ((x + d) / d), d);
  }

  lemma lemma_add_mul_div(a: int, b: int, d: int)
  requires d > 0
  ensures (a + b*d) / d == a/d + b
  {
    if (b == 0) {
      assert (a + 0*d) / d == a/d;
      assert a/d + 0 == a/d;
    } else if (b > 0) {
      lemma_add_mul_div(a, b-1, d);
      lemma_div_ind(a + (b-1)*d, d);
      assert (a + b*d) / d == ((a + (b-1)*d) + d) / d;
      assert ((a + (b-1)*d) / d) + 1 == (a + b*d) / d;
      assert (a/d + (b-1)) + 1 == a/d + b;
      assert (a + b*d) / d == a/d + b;
    } else {
      lemma_add_mul_div(a, b+1, d);
      lemma_div_ind(a + b*d, d);
      assert (a + b*d) / d == ((a + (b+1)*d) - d) / d;
      assert ((a + (b+1)*d) / d) - 1 == (a + b*d) / d;
      assert (a/d + (b+1)) - 1 == a/d + b;
      assert (a + b*d) / d == a/d + b;
    }
  }

  lemma lemma_div_multiples_vanish_fancy(x:int, b:int, d:int)
      requires 0<d;
      requires 0<=b<d;
      ensures (d*x + b)/d == x;
  {
    if (x == 0) {
      assert (d*0 + b)/d == b/d;
      assert 0 <= b < d;
      assert b/d == 0;
      assert (d*0 + b)/d == 0;
    } else if (x > 0) {
      lemma_div_multiples_vanish_fancy(x-1, b, d);
      lemma_div_ind(d*(x-1) + b, d);
      assert (d*x + b)/d == ((d*(x-1) + b) + d)/d;
      assert ((d*(x-1) + b)/d) + 1 == (d*x + b)/d;
      assert (x-1) + 1 == x;
      assert (d*x + b)/d == x;
    } else {
      lemma_div_multiples_vanish_fancy(x+1, b, d);
      lemma_div_ind(d*x + b, d);
      assert (d*x + b)/d == ((d*(x+1) + b) - d)/d;
      assert ((d*(x+1) + b)/d) - 1 == (d*x + b)/d;
      assert (x+1) - 1 == x;
      assert (d*x + b)/d == x;
    }
  }

  lemma lemma_div_by_multiple(b:int, d:int)
      requires 0 < d;
      ensures  (b*d) / d == b;
  {   
      lemma_div_multiples_vanish_fancy(b, 0, d);
      assert (b*d + 0)/d == b;
      assert (b*d)/d == b;
  }

  lemma lemma_mod_multiples_basic(x:int, m:int)
      requires m > 0;
      ensures  (x * m) % m == 0;
  {
    lemma_div_by_multiple(x, m);
    assert (x*m)/m == x;
    assert (x*m) % m == 0;
        == 0;
  }

  lemma lemma_div_by_multiple_is_strongly_ordered(x:int, y:int, m:int, z:int)
      requires x < y;
      requires y == m * z;
      requires z > 0;
      ensures     x / z < y / z;
  {
    lemma_mod_multiples_basic(m, z);
    // strongest invariant: y == m*z, m > 0, z > 0, x < y
    if (x / z <= m-1) {
      assert x / z < m;
      assert y / z == (m*z)/z == m;
      assert x / z < y / z;
    } else {
      assert x / z > m-1;
      lemma_div_by_multiple_is_strongly_ordered(x, y-z, m-1, z);
      assert (y-z) == (m-1)*z;
      assert x < y-z+z == y;
      assert x / z < (y-z)/z;
      assert (y-z)/z < y/z;
      assert x / z < y / z;
    }
  }

  lemma lemma_power2_div_is_sub(x:int, y:int)
      requires 0 <= x <= y;
      ensures power2(y - x) == power2(y) / power2(x)
        >= 0;
  {
    calc {
        power2(y) / power2(x);
        { lemma_power2_adds(y-x, x); }
        (power2(y-x)*power2(x)) / power2(x);
        { lemma_div_by_multiple(power2(y-x), power2(x)); }
        power2(y-x);
    }
    assert power2(y-x) == power2(y) / power2(x);
    assert power2(y-x) >= 0;
  }

  lemma lemma_div_denominator(x:int,c:nat,d:nat)
      requires 0 <= x;
      requires 0<c;
      requires 0<d;
      ensures c * d != 0;
      ensures (x/c)/d == x / (c*d);
  {
    assert c * d != 0;
    if (x < c*d) {
      assert x/c < d;
      assert (x/c)/d == 0;
      assert x < c*d;
      assert x/(c*d) == 0;
      assert (x/c)/d == x/(c*d);
    } else {
      calc {
        (x / c) / d;
        ((x - c*d + c*d) / c) / d;
        {
          lemma_add_mul_div(x-c*d, d, c);
        }
        ((x - c*d) / c + d) / d;
        {
          lemma_div_ind((x - c*d) / c, d);
        }
        ((x - c*d) / c) / d + 1;
        {
          lemma_div_denominator(x - c*d, c, d);
        }
        ((x - c*d) / (c*d)) + 1;
        {
          lemma_div_ind(x - c*d, c*d);
        }
        x / (c*d);
      }
      assert (x/c)/d == x/(c*d);
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
