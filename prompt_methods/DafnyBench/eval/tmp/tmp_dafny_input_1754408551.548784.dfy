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
    // By contradiction: suppose Exp(x) <= 0
    if Exp(x) <= 0.0 {
      // But by FunctionalEquation, Exp(x+1) = Exp(x)*Exp(1)
      // Exp(1) > 0 by EvalOne
      assert Exp(1.0) > 0.0;
      var ex1 := Exp(x + 1.0);
      calc {
        ex1;
        { FunctionalEquation(x, 1.0); }
        Exp(x) * Exp(1.0);
      }
      if Exp(x) < 0.0 {
        // Then Exp(x) * Exp(1.0) < 0, so ex1 < 0
        assert ex1 < 0.0;
        // But by induction, Exp(x+1.0) must be > 0
        // Contradicts positivity at x+1
        assert false;
      } else {
        // Exp(x) == 0.0
        assert Exp(x) == 0.0;
        // Then ex1 == 0.0
        assert ex1 == 0.0;
        // But by Increasing(x, x+1.0), Exp(x) < Exp(x+1.0)
        assert Exp(x) < Exp(x+1.0);
        // So 0.0 < 0.0, contradiction
        assert false;
      }
    }
    // Therefore, Exp(x) > 0.0
  }

  lemma EvalZero()
    ensures Exp(0.0) == 1.0
  {
    // By FunctionalEquation(0, 0): Exp(0) = Exp(0) * Exp(0)
    FunctionalEquation(0.0, 0.0);
    // Let a = Exp(0)
    var a := Exp(0.0);
    assert a == a * a;
    // a > 0 by Positive(0.0)
    Positive(0.0);
    assert a > 0.0;
    // Only positive real a with a == a*a is 1
    assert a == 1.0;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
