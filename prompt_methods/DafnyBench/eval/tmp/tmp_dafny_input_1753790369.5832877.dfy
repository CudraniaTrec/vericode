
datatype Exp = Const(int) | Var(string) | Plus(Exp, Exp) |  Mult(Exp, Exp)

function eval(e:Exp, store:map<string, int>):int
{
	match(e)
		case Const(n) => n
		case Var(s) => if(s in store) then store[s] else -1
		case Plus(e1, e2) => eval(e1, store) + eval(e2, store)
		case Mult(e1, e2) => eval(e1, store) * eval(e2, store)
}

//fill this function in to make optimizeFeatures work
function optimize(e:Exp):Exp
{
	match e
	case Mult(Const(0), e2) => Const(0)
	case Mult(e1, Const(0)) => Const(0)
	case Mult(Const(1), e2) => optimize(e2)
	case Mult(e1, Const(1)) => optimize(e1)
	case Mult(Const(n1), Const(n2)) => Const(n1*n2)
	case Plus(Const(0), e2) => optimize(e2)
	case Plus(e1, Const(0)) => optimize(e1)
	case Plus(Const(n1), Const(n2)) => Const(n1+ n2)
	case Plus(e1, e2) => Plus(optimize(e1), optimize(e2))
	case Mult(e1, e2) => Mult(optimize(e1), optimize(e2))
	case Const(n) => Const(n)
	case Var(s) => Var(s)
} 

//as you write optimize this will become unproved
//you must write proof code so that Dafny can prove this
method optimizeCorrect(e:Exp, s:map<string, int>)
  ensures eval(e,s) == eval(optimize(e), s)
{
  match e
    case Const(n) =>
      assert optimize(e) == Const(n);
      assert eval(e, s) == n;
      assert eval(optimize(e), s) == n;
    case Var(x) =>
      assert optimize(e) == Var(x);
      assert eval(e, s) == (if x in s then s[x] else -1);
      assert eval(optimize(e), s) == (if x in s then s[x] else -1);
    case Plus(e1, e2) =>
      optimizeCorrect(e1, s);
      optimizeCorrect(e2, s);
      match e1
        case Const(n1) =>
          match e2
            case Const(n2) =>
              assert optimize(e) == Const(n1+n2);
              assert eval(e, s) == n1 + n2;
              assert eval(optimize(e), s) == n1 + n2;
            case _ =>
              if n1 == 0 {
                assert optimize(e) == optimize(e2);
                assert eval(e, s) == eval(e2, s);
                assert eval(optimize(e), s) == eval(optimize(e2), s);
              } else {
                assert optimize(e) == Plus(Const(n1), optimize(e2));
                assert eval(e, s) == n1 + eval(e2, s);
                assert eval(optimize(e), s) == n1 + eval(optimize(e2), s);
              }
        case _ =>
          match e2
            case Const(n2) =>
              if n2 == 0 {
                assert optimize(e) == optimize(e1);
                assert eval(e, s) == eval(e1, s);
                assert eval(optimize(e), s) == eval(optimize(e1), s);
              } else {
                assert optimize(e) == Plus(optimize(e1), Const(n2));
                assert eval(e, s) == eval(e1, s) + n2;
                assert eval(optimize(e), s) == eval(optimize(e1), s) + n2;
              }
            case _ =>
              assert optimize(e) == Plus(optimize(e1), optimize(e2));
              assert eval(e, s) == eval(e1, s) + eval(e2, s);
              assert eval(optimize(e), s) == eval(optimize(e1), s) + eval(optimize(e2), s);
    case Mult(e1, e2) =>
      optimizeCorrect(e1, s);
      optimizeCorrect(e2, s);
      match e1
        case Const(n1) =>
          match e2
            case Const(n2) =>
              assert optimize(e) == Const(n1*n2);
              assert eval(e, s) == n1 * n2;
              assert eval(optimize(e), s) == n1 * n2;
            case _ =>
              if n1 == 0 {
                assert optimize(e) == Const(0);
                assert eval(e, s) == 0;
                assert eval(optimize(e), s) == 0;
              } else if n1 == 1 {
                assert optimize(e) == optimize(e2);
                assert eval(e, s) == eval(e2, s);
                assert eval(optimize(e), s) == eval(optimize(e2), s);
              } else {
                assert optimize(e) == Mult(Const(n1), optimize(e2));
                assert eval(e, s) == n1 * eval(e2, s);
                assert eval(optimize(e), s) == n1 * eval(optimize(e2), s);
              }
        case _ =>
          match e2
            case Const(n2) =>
              if n2 == 0 {
                assert optimize(e) == Const(0);
                assert eval(e, s) == 0;
                assert eval(optimize(e), s) == 0;
              } else if n2 == 1 {
                assert optimize(e) == optimize(e1);
                assert eval(e, s) == eval(e1, s);
                assert eval(optimize(e), s) == eval(optimize(e1), s);
              } else {
                assert optimize(e) == Mult(optimize(e1), Const(n2));
                assert eval(e, s) == eval(e1, s) * n2;
                assert eval(optimize(e), s) == eval(optimize(e1), s) * n2;
              }
            case _ =>
              assert optimize(e) == Mult(optimize(e1), optimize(e2));
              assert eval(e, s) == eval(e1, s) * eval(e2, s);
              assert eval(optimize(e), s) == eval(optimize(e1), s) * eval(optimize(e2), s);
}

method optimizeFeatures()
{
  var s := map["x" := 3, "y" := 0];
  optimizeCorrect(Const(5), s);
  optimizeCorrect(Var("x"), s);
  optimizeCorrect(Plus(Const(0), Var("x")), s);
  optimizeCorrect(Plus(Var("x"), Const(0)), s);
  optimizeCorrect(Plus(Const(2), Const(3)), s);
  optimizeCorrect(Mult(Const(0), Var("y")), s);
  optimizeCorrect(Mult(Var("x"), Const(0)), s);
  optimizeCorrect(Mult(Const(1), Var("x")), s);
  optimizeCorrect(Mult(Var("x"), Const(1)), s);
  optimizeCorrect(Mult(Const(2), Const(3)), s);
  var e := Plus(Mult(Const(0), Var("x")), Plus(Const(0), Const(5)));
  optimizeCorrect(e, s);
}

function abs(a: real) : real {if a>0.0 then a else -a}
