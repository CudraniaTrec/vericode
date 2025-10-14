
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
		assert optimize(e) == e;
		assert eval(e, s) == eval(optimize(e), s);

	case Var(x) =>
		// optimize(Var(x)) == Var(x)
		assert optimize(e) == e;
		assert eval(e, s) == eval(optimize(e), s);

	case Plus(e1, e2) =>
		optimizeCorrect(e1, s);
		optimizeCorrect(e2, s);
		match e1
		case Const(n1) =>
			match e2
			case Const(n2) =>
				// optimize(Plus(Const(n1), Const(n2))) == Const(n1+n2)
				assert optimize(e) == Const(n1+n2);
				assert eval(e, s) == n1 + n2;
				assert eval(optimize(e), s) == n1 + n2;
			case _ =>
				if n1 == 0 {
					// optimize(Plus(Const(0), e2)) == optimize(e2)
					assert optimize(e) == optimize(e2);
					assert eval(e, s) == eval(e2, s);
					assert eval(optimize(e), s) == eval(optimize(e2), s);
				} else {
					// optimize(Plus(Const(n1), e2)) == Plus(Const(n1), optimize(e2))
					assert optimize(e) == Plus(Const(n1), optimize(e2));
					assert eval(e, s) == n1 + eval(e2, s);
					assert eval(optimize(e), s) == n1 + eval(optimize(e2), s);
				}
		case _ =>
			match e2
			case Const(n2) =>
				if n2 == 0 {
					// optimize(Plus(e1, Const(0))) == optimize(e1)
					assert optimize(e) == optimize(e1);
					assert eval(e, s) == eval(e1, s);
					assert eval(optimize(e), s) == eval(optimize(e1), s);
				} else {
					// optimize(Plus(e1, Const(n2))) == Plus(optimize(e1), Const(n2))
					assert optimize(e) == Plus(optimize(e1), Const(n2));
					assert eval(e, s) == eval(e1, s) + n2;
					assert eval(optimize(e), s) == eval(optimize(e1), s) + n2;
				}
			case _ =>
				// optimize(Plus(e1, e2)) == Plus(optimize(e1), optimize(e2))
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
				// optimize(Mult(Const(n1), Const(n2))) == Const(n1*n2)
				assert optimize(e) == Const(n1*n2);
				assert eval(e, s) == n1 * n2;
				assert eval(optimize(e), s) == n1 * n2;
			case _ =>
				if n1 == 0 {
					// optimize(Mult(Const(0), e2)) == Const(0)
					assert optimize(e) == Const(0);
					assert eval(e, s) == 0;
					assert eval(optimize(e), s) == 0;
				} else if n1 == 1 {
					// optimize(Mult(Const(1), e2)) == optimize(e2)
					assert optimize(e) == optimize(e2);
					assert eval(e, s) == eval(e2, s);
					assert eval(optimize(e), s) == eval(optimize(e2), s);
				} else {
					// optimize(Mult(Const(n1), e2)) == Mult(Const(n1), optimize(e2))
					assert optimize(e) == Mult(Const(n1), optimize(e2));
					assert eval(e, s) == n1 * eval(e2, s);
					assert eval(optimize(e), s) == n1 * eval(optimize(e2), s);
				}
		case _ =>
			match e2
			case Const(n2) =>
				if n2 == 0 {
					// optimize(Mult(e1, Const(0))) == Const(0)
					assert optimize(e) == Const(0);
					assert eval(e, s) == 0;
					assert eval(optimize(e), s) == 0;
				} else if n2 == 1 {
					// optimize(Mult(e1, Const(1))) == optimize(e1)
					assert optimize(e) == optimize(e1);
					assert eval(e, s) == eval(e1, s);
					assert eval(optimize(e), s) == eval(optimize(e1), s);
				} else {
					// optimize(Mult(e1, Const(n2))) == Mult(optimize(e1), Const(n2))
					assert optimize(e) == Mult(optimize(e1), Const(n2));
					assert eval(e, s) == eval(e1, s) * n2;
					assert eval(optimize(e), s) == eval(optimize(e1), s) * n2;
				}
			case _ =>
				// optimize(Mult(e1, e2)) == Mult(optimize(e1), optimize(e2))
				assert optimize(e) == Mult(optimize(e1), optimize(e2));
				assert eval(e, s) == eval(e1, s) * eval(e2, s);
				assert eval(optimize(e), s) == eval(optimize(e1), s) * eval(optimize(e2), s);
}

method optimizeFeatures()
{
	// Test cases for optimizeCorrect
	var s := map["x" := 3, "y" := 0];
	assert eval(Const(5), s) == eval(optimize(Const(5)), s);
	assert eval(Var("x"), s) == eval(optimize(Var("x")), s);
	assert eval(Plus(Const(0), Var("x")), s) == eval(optimize(Plus(Const(0), Var("x"))), s);
	assert eval(Plus(Var("x"), Const(0)), s) == eval(optimize(Plus(Var("x"), Const(0))), s);
	assert eval(Plus(Const(2), Const(3)), s) == eval(optimize(Plus(Const(2), Const(3))), s);
	assert eval(Mult(Const(0), Var("y")), s) == eval(optimize(Mult(Const(0), Var("y"))), s);
	assert eval(Mult(Var("x"), Const(0)), s) == eval(optimize(Mult(Var("x"), Const(0))), s);
	assert eval(Mult(Const(1), Var("x")), s) == eval(optimize(Mult(Const(1), Var("x"))), s);
	assert eval(Mult(Var("x"), Const(1)), s) == eval(optimize(Mult(Var("x"), Const(1))), s);
	assert eval(Mult(Const(2), Const(3)), s) == eval(optimize(Mult(Const(2), Const(3))), s);

	// Inductive test
	var e := Plus(Mult(Const(0), Var("x")), Plus(Const(0), Const(5)));
	optimizeCorrect(e, s);
}

function abs(a: real) : real {if a>0.0 then a else -a}
