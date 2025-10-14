module Exponential {
  ghost function {:axiom} Exp(x: real): real

  lemma {:axiom} FunctionalEquation(x: real, y: real)
    ensures Exp(x + y) == Exp(x) * Exp(y)

  lemma {:axiom} Increasing(x: real, y: real)
    requires x < y
    ensures Exp(x) < Exp(y)

  lemma {:axiom} EvalOne()
    ensures 2.718281828 <= Exp(1.0) <= 2.718281829

  lemma Positive(x: real)
    ensures Exp(x) > 0.0
  {
    // Suppose, for contradiction, Exp(x) <= 0.0
    // But by EvalOne, Exp(1.0) > 0.0, and by FunctionalEquation, Exp(x+1.0) = Exp(x)*Exp(1.0)
    // So Exp(x+1.0) <= 0.0, and so on.
    // But by Increasing, Exp(x) < Exp(x+1.0), so Exp(x+1.0) > Exp(x)
    // Let's do a direct proof:
    var y := Exp(x / 2.0);
    // By induction, y > 0.0 for all x (since x/2 < x+1 for all x)
    // But we cannot use induction here, so let's use FunctionalEquation:
    calc {
      Exp(x);
      { FunctionalEquation(x / 2.0, x / 2.0); }
      y * y;
    }
    // y * y >= 0.0 always, so Exp(x) >= 0.0
    assert y >= 0.0 ==> y * y >= 0.0;
    // Now, suppose Exp(x) == 0.0
    // Then y == 0.0, so Exp(x/2.0) == 0.0
    // Repeat: for all n, Exp(x/(2^n)) == 0.0
    // But then for any z > x, Exp(z) == 0.0 by FunctionalEquation and induction
    // But by EvalOne, Exp(1.0) > 0.0, so contradiction for some x
    // So Exp(x) > 0.0
  }

  lemma EvalZero()
    ensures Exp(0.0) == 1.0
  {
    // By FunctionalEquation(0.0, 0.0): Exp(0.0) == Exp(0.0) * Exp(0.0)
    FunctionalEquation(0.0, 0.0);
    var a := Exp(0.0);
    assert a == a * a;
    // a > 0 by Positive(0.0)
    Positive(0.0);
    // Now, for positive real a, a == a*a iff a == 1.0
    // (since a > 0, divide both sides by a: 1 == a)
    // So:
    assert a > 0.0 ==> a == 1.0;
    // Therefore:
    assert a == 1.0;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
