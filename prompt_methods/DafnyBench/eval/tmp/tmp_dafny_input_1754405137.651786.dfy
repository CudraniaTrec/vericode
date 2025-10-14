
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
	case Mult(Const(0), e) => Const(0)
	case Mult(e, Const(0)) => Const(0)
	case Mult(Const(1), e) => e
	case Mult(e, Const(1)) => e
	case Mult(Const(n1), Const(n2)) => Const(n1*n2)
	case Plus(Const(0), e) => e
	case Plus(e, Const(0)) => e
	case Plus(Const(n1), Const(n2)) => Const(n1+ n2)
	case e => e

} 

//as you write optimize this will become unproved
//you must write proof code so that Dafny can prove this
method optimizeCorrect(e:Exp, s:map<string, int>)
ensures eval(e,s) == eval(optimize(e), s)
{
	match e
	case Const(n) =>
		// optimize(Const(n)) == Const(n)
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
		var oe1 := optimize(e1);
		var oe2 := optimize(e2);
		match e
		case Plus(Const(0), e2) =>
			assert optimize(e) == optimize(e2);
			assert eval(e, s) == eval(e2, s);
			assert eval(optimize(e), s) == eval(optimize(e2), s);
		case Plus(e1, Const(0)) =>
			assert optimize(e) == optimize(e1);
			assert eval(e, s) == eval(e1, s);
			assert eval(optimize(e), s) == eval(optimize(e1), s);
		case Plus(Const(n1), Const(n2)) =>
			assert optimize(e) == Const(n1 + n2);
			assert eval(e, s) == n1 + n2;
			assert eval(optimize(e), s) == n1 + n2;
		case _ =>
			assert optimize(e) == Plus(oe1, oe2);
			assert eval(e, s) == eval(e1, s) + eval(e2, s);
			assert eval(optimize(e), s) == eval(oe1, s) + eval(oe2, s);
			assert eval(e, s) == eval(optimize(e), s);
	case Mult(e1, e2) =>
		optimizeCorrect(e1, s);
		optimizeCorrect(e2, s);
		var oe1 := optimize(e1);
		var oe2 := optimize(e2);
		match e
		case Mult(Const(0), e2) =>
			assert optimize(e) == Const(0);
			assert eval(e, s) == 0;
			assert eval(optimize(e), s) == 0;
		case Mult(e1, Const(0)) =>
			assert optimize(e) == Const(0);
			assert eval(e, s) == 0;
			assert eval(optimize(e), s) == 0;
		case Mult(Const(1), e2) =>
			assert optimize(e) == optimize(e2);
			assert eval(e, s) == eval(e2, s);
			assert eval(optimize(e), s) == eval(optimize(e2), s);
		case Mult(e1, Const(1)) =>
			assert optimize(e) == optimize(e1);
			assert eval(e, s) == eval(e1, s);
			assert eval(optimize(e), s) == eval(optimize(e1), s);
		case Mult(Const(n1), Const(n2)) =>
			assert optimize(e) == Const(n1 * n2);
			assert eval(e, s) == n1 * n2;
			assert eval(optimize(e), s) == n1 * n2;
		case _ =>
			assert optimize(e) == Mult(oe1, oe2);
			assert eval(e, s) == eval(e1, s) * eval(e2, s);
			assert eval(optimize(e), s) == eval(oe1, s) * eval(oe2, s);
			assert eval(e, s) == eval(optimize(e), s);
}

method optimizeFeatures()
{
	// Test all features of optimize
	var s := map["x" := 3, "y" := 0];
	assert optimize(Const(5)) == Const(5);
	assert optimize(Var("x")) == Var("x");
	assert optimize(Plus(Const(0), Var("x"))) == Var("x");
	assert optimize(Plus(Var("x"), Const(0))) == Var("x");
	assert optimize(Plus(Const(2), Const(3))) == Const(5);
	assert optimize(Mult(Const(0), Var("x"))) == Const(0);
	assert optimize(Mult(Var("x"), Const(0))) == Const(0);
	assert optimize(Mult(Const(1), Var("x"))) == Var("x");
	assert optimize(Mult(Var("x"), Const(1))) == Var("x");
	assert optimize(Mult(Const(2), Const(3))) == Const(6);
	assert optimize(Plus(Var("x"), Var("y"))) == Plus(Var("x"), Var("y"));
	assert optimize(Mult(Var("x"), Var("y"))) == Mult(Var("x"), Var("y"));

	// Check correctness for some examples
	optimizeCorrect(Const(5), s);
	optimizeCorrect(Var("x"), s);
	optimizeCorrect(Plus(Const(0), Var("x")), s);
	optimizeCorrect(Plus(Var("x"), Const(0)), s);
	optimizeCorrect(Plus(Const(2), Const(3)), s);
	optimizeCorrect(Mult(Const(0), Var("x")), s);
	optimizeCorrect(Mult(Var("x"), Const(0)), s);
	optimizeCorrect(Mult(Const(1), Var("x")), s);
	optimizeCorrect(Mult(Var("x"), Const(1)), s);
	optimizeCorrect(Mult(Const(2), Const(3)), s);
	optimizeCorrect(Plus(Var("x"), Var("y")), s);
	optimizeCorrect(Mult(Var("x"), Var("y")), s);
}

function abs(a: real) : real {if a>0.0 then a else -a}
