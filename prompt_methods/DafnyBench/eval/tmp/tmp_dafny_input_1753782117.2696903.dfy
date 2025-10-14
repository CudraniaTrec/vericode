
// Noa Leron 207131871
// Tsuri Farhana 315016907


// definitions borrowed from Rustan Leino's Program Proofs Chapter 7
// (https://program-proofs.com/code.html example code in Dafny; source file 7-Unary.dfy)
datatype Unary = Zero | Suc(pred: Unary)

ghost function UnaryToNat(x: Unary): nat {
  match x
  case Zero => 0
  case Suc(x') => 1 + UnaryToNat(x')
}

ghost function NatToUnary(n: nat): Unary {
  if n == 0 then Zero else Suc(NatToUnary(n-1))
}

lemma NatUnaryCorrespondence(n: nat, x: Unary)
  ensures UnaryToNat(NatToUnary(n)) == n
  ensures NatToUnary(UnaryToNat(x)) == x
{
  if n == 0 {
  } else {
    NatUnaryCorrespondence(n-1, x);
  }
}

predicate Less(x: Unary, y: Unary) {
  y != Zero && (x.Suc? ==> Less(x.pred, y.pred))
}

predicate LessAlt(x: Unary, y: Unary) {
  y != Zero && (x == Zero || Less(x.pred, y.pred))
}

lemma LessSame(x: Unary, y: Unary)
  ensures Less(x, y) == LessAlt(x, y)
{
  if y == Zero {
  } else if x == Zero {
  } else {
    LessSame(x.pred, y.pred);
  }
}

lemma LessCorrect(x: Unary, y: Unary)
  ensures Less(x, y) <==> UnaryToNat(x) < UnaryToNat(y)
{
  if y == Zero {
  } else if x == Zero {
  } else {
    LessCorrect(x.pred, y.pred);
  }
}

lemma LessTransitive(x: Unary, y: Unary, z: Unary)
  requires Less(x, y) && Less(y, z)
  ensures Less(x, z)
{
  if z == Zero {
    // contradiction: Less(y, z) requires z != Zero
  } else if x == Zero {
    // Less(Zero, z) holds if z != Zero
  } else if y == Zero {
    // contradiction: Less(x, y) requires y != Zero
  } else {
    LessTransitive(x.pred, y.pred, z.pred);
  }
}

function Add(x: Unary, y: Unary): Unary {
  match y
  case Zero => x
  case Suc(y') => Suc(Add(x, y'))
}

lemma {:induction false} SucAdd(x: Unary, y: Unary)
  ensures Suc(Add(x, y)) == Add(Suc(x), y)
{
  match y
  case Zero =>
  case Suc(y') =>
    calc {
      Suc(Add(x, Suc(y')));
    ==  // def. Add
      Suc(Suc(Add(x, y')));
    ==  { SucAdd(x, y'); }
      Suc(Add(Suc(x), y'));
    ==  // def. Add
      Add(Suc(x), Suc(y'));
    }
}

lemma {:induction false} AddZero(x: Unary)
  ensures Add(Zero, x) == x
{
  match x
  case Zero =>
  case Suc(x') =>
    calc {
      Add(Zero, Suc(x'));
    ==  // def. Add
      Suc(Add(Zero, x'));
    ==  { AddZero(x'); }
      Suc(x');
    }
}

function Sub(x: Unary, y: Unary): Unary
  requires !Less(x, y)
{
  match y
  case Zero => x
  case Suc(y') => Sub(x.pred, y')
}

function Mul(x: Unary, y: Unary): Unary {
  match x
  case Zero => Zero
  case Suc(x') => Add(Mul(x', y), y)
}

lemma SubStructurallySmaller(x: Unary, y: Unary)
  requires !Less(x, y) && y != Zero
  ensures Less(Sub(x, y), x)
{
  if y == Zero {
    // contradiction: y != Zero
  } else if x == Zero {
    // contradiction: !Less(x, y) is false if x == Zero and y != Zero
  } else if y.pred == Zero {
    // y = Suc(Zero)
    assert Sub(x, y) == x.pred;
    assert Less(x.pred, x);
  } else {
    // y = Suc(y')
    SubStructurallySmaller(x.pred, y.pred);
    assert Sub(x, y) == Sub(x.pred, y.pred);
    assert Less(Sub(x.pred, y.pred), x.pred);
    assert Less(Sub(x, y), x);
  }
}

lemma AddSub(x: Unary, y: Unary)
  requires !Less(x, y)
  ensures Add(Sub(x, y), y) == x
{
  if y == Zero {
    assert Sub(x, y) == x;
    assert Add(Sub(x, y), y) == Add(x, Zero);
    assert Add(x, Zero) == x;
  } else {
    AddSub(x.pred, y.pred);
    assert Sub(x, y) == Sub(x.pred, y.pred);
    assert Add(Sub(x, y), y) == Add(Sub(x.pred, y.pred), Suc(y.pred));
    assert Add(Sub(x.pred, y.pred), Suc(y.pred)) == Suc(Add(Sub(x.pred, y.pred), y.pred));
    assert Add(Sub(x.pred, y.pred), y.pred) == x.pred;
    assert Suc(x.pred) == x;
  }
}

method IterativeDivMod(x: Unary, y: Unary) returns (d: Unary, m: Unary)
  requires y != Zero
  ensures Add(Mul(d, y), m) == x && Less(m, y)
{
  if (Less(x, y)) {
    AddZero(x);
    d := Zero;
    m := x;
    // assert Add(Mul(d, y), m) == x;
    // assert Less(m, y);
  }
  else {
    var x0: Unary := x;
    d := Zero;
    AddZero(x);

    while (!Less(x0, y))
      invariant Add(Mul(d, y), x0) == x
      invariant d == NatToUnary(UnaryToNat(x) - UnaryToNat(x0)) // d counts how many y's subtracted
      invariant Less(x0, x) || x0 == x
      invariant y != Zero
      decreases UnaryToNat(x0)
    {
      AddMulSucSubEqAddMul(d, y, x0);
      d := Suc(d);
      SubStructurallySmaller(x0, y);
      x0 := Sub(x0, y);
    }
    m := x0;
    // assert Add(Mul(d, y), m) == x;
    // assert Less(m, y);
  }
}

lemma AddMulEqMulSuc(a: Unary, b: Unary)
  ensures Mul(Suc(a), b) == Add(Mul(a, b), b)
{
  calc{
    Mul(Suc(a), b);
    == // def. Mul
    Add(Mul(a, b), b);
  }
}

lemma AddMulSucSubEqAddMul(d: Unary, y: Unary, x0: Unary)
  requires !Less(x0, y)
  requires y != Zero
  ensures Add(Mul(Suc(d), y), Sub(x0, y)) == Add(Mul(d, y), x0)
{
  calc{
    Add(Mul(Suc(d), y), Sub(x0, y));
    == {AddMulEqMulSuc(d, y);}
    Add(Add(Mul(d, y), y), Sub(x0, y));
    == {AddTransitive(Mul(d, y), y, Sub(x0, y));}
    Add(Mul(d, y), Add(y, Sub(x0, y)));
    == {AddCommutative(Sub(x0, y), y);}
    Add(Mul(d, y), Add(Sub(x0, y), y));
    == {AddSub(x0, y);}
    Add(Mul(d, y), x0);
  }
}

lemma AddTransitive(a: Unary, b: Unary, c: Unary)
  ensures Add(a, Add(b, c)) == Add(Add(a, b), c)
{
  match c 
  case Zero =>
    calc{
      Add(a, Add(b, c));
      == 
      Add(a, Add(b, Zero));
      == // def. Add
      Add(a, b);
      == // def. Add
      Add(Add(a,b), Zero);
      == 
      Add(Add(a,b), c);
    }
  case Suc(c') =>
    match b
    case Zero =>
      calc{
        Add(a, Add(b, c));
        == 
        Add(a, Add(Zero, Suc(c')));
        == {AddZero(Suc(c'));}
        Add(a, Suc(c'));
        == // def. Add
        Add(Add(a, Zero), Suc(c'));
        ==
        Add(Add(a, b), Suc(c'));
        ==
        Add(Add(a,b), c);
      }
    case Suc(b') =>
      match a
      case Zero =>
        calc{
          Add(a, Add(b, c));
          ==
          Add(Zero, Add(Suc(b'), Suc(c')));
          == {AddZero(Add(Suc(b'), Suc(c')));}
          Add(Suc(b'), Suc(c'));
          == {AddZero(Suc(b'));}
          Add(Add(Zero, Suc(b')), Suc(c'));
          ==
          Add(Add(a, b), c);
        }
      case Suc(a') =>
        calc{
          Add(a, Add(b, c));
          ==
          Add(Suc(a'), Add(Suc(b'), Suc(c')));
          == // def. Add
          Add(Suc(a'), Suc(Add(Suc(b'), c')));
          == // def. Add
          Suc(Add(Suc(a'), Add(Suc(b'), c')));
          == {SucAdd(a', Add(Suc(b'), c'));}
          Suc(Suc(Add(a', Add(Suc(b'), c'))));
          == {SucAdd(b', c');}
          Suc(Suc(Add(a', Suc(Add(b', c')))));
          == // def. Add
          Suc(Suc(Suc(Add(a', Add(b', c')))));
          == {AddTransitive(a', b', c');}
          Suc(Suc(Suc(Add(Add(a',b'), c'))));
          == // def. Add
          Suc(Suc(Add(Add(a', b'), Suc(c'))));
          == {SucAdd(Add(a', b'), Suc(c'));}
          Suc(Add(Suc(Add(a', b')), Suc(c')));
          == {SucAdd(a', b');}
          Suc(Add(Add(Suc(a'), b'), Suc(c')));
          == {SucAdd(Add(Suc(a'), b'), Suc(c'));}
          Add(Suc(Add(Suc(a'), b')), Suc(c'));
          == // def. Add
          Add(Add(Suc(a'), Suc(b')), Suc(c'));
          ==
          Add(Add(a,b), c);
        }
}

lemma AddCommutative(a: Unary, b: Unary)
  ensures Add(a, b) == Add(b, a)
{
  match b
  case Zero => 
    calc{
      Add(a, b);
      ==
      Add(a, Zero);
      == // def. Add
      a;
      == {AddZero(a);}
      Add(Zero, a);
      ==
      Add(b, a);
    }
  case Suc(b') =>
    calc{
      Add(a, b);
      ==
      Add(a, Suc(b'));
      == // def. Add
      Suc(Add(a, b'));
      == {AddCommutative(a, b');}
      Suc(Add(b', a));
      == {SucAdd(b', a);}
      Add(Suc(b'), a);
      ==
      Add(b, a);
    }
}

method Main() {
  var U3 := Suc(Suc(Suc(Zero)));
  var U7 := Suc(Suc(Suc(Suc(U3))));
  var d, m := IterativeDivMod(U7, U3);
  print "Just as 7 divided by 3 is 2 with a remainder of 1, IterativeDivMod(", U7, ", ", U3, ") is ", d, " with a remainder of ", m;
}

function abs(a: real) : real {if a>0.0 then a else -a}
