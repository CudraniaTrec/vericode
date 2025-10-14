// -------------------------------------------------------------
// 1. Implementing type inference
// -------------------------------------------------------------

// Syntax:
//
// τ := Int | Bool | τ1->τ2
// e ::= x | λx : τ.e | true| false| e1 e2 | if e then e1 else e2
// v ::= true | false | λx : τ.e
// E ::= [·] | E e | v E | if E then e1 else e2
type VarName = string

type TypeVar = Type -> Type

datatype Type = Int | Bool | TypeVar

datatype Exp =
    | Var(x: VarName)
    | Lam(x: VarName, t: Type, e: Exp)
    | App(e1: Exp, e2:Exp)
    | True()
    | False()
    | Cond(e0: Exp, e1: Exp, e2: Exp)

datatype Value =
    | TrueB()
    | FalseB()
    | Lam(x: VarName, t: Type, e: Exp)

datatype Eva = 
    | E()
    | EExp(E : Eva, e : Exp)
    | EVar(v : Value, E : Eva)
    | ECond(E:Eva, e1 : Exp, e2 : Exp)

function FV(e: Exp): set<VarName> {
    match(e) {
        case Var(x) => {x}
        case Lam(x, t, e) => FV(e) - {x}
        case App(e1,e2) => FV(e1) + FV(e2)
        case True() => {}
        case False() => {}
        case Cond(e0, e1, e2) => FV(e0) + FV(e1) + FV(e2)
    }
}
// Typing rules system
// -------------------------------------------------------------
// Typing rules system
type Env = map<VarName, Type>

predicate hasType(gamma: Env, e: Exp, t: Type)
{
    match e {
        case Var(x) =>  x in gamma && t == gamma[x]
        case Lam(x, t1, e1) => (exists t2 :: hasType(gamma[x := t1], e1, t2)) && t == TypeVar
        case App(e1, e2) => (exists t1', t2' :: hasType(gamma, e1, t1') && hasType(gamma, e2, t2') && t1' == TypeVar && t == t2')
        case True() => t == Bool
        case False() => t == Bool
        case Cond(e0, e1, e2) => hasType(gamma, e0, Bool) && hasType(gamma, e1, t) && hasType(gamma, e2, t)
    }    
}

// -----------------------------------------------------------------
// 2. Extending While with tuples
// -----------------------------------------------------------------


lemma {:induction false} extendGamma(gamma: Env, e: Exp, t: Type, x1: VarName, t1: Type)
    requires hasType(gamma, e, t)
    requires x1 !in FV(e)
    ensures hasType(gamma[x1 := t1], e, t)
{
    match e {
        case Var(x) => {
            assert x in gamma;
            assert t == gamma[x];
            assert x != x1; // since x1 !in FV(e) and FV(Var(x)) == {x}
            assert gamma[x] == (gamma[x1 := t1])[x];
            assert hasType(gamma[x1 := t1], e, t);
        }
        case True() => {
            assert t == Bool;
            assert hasType(gamma[x1 := t1], e, t);
        }
        case False() => {
            assert t == Bool;
            assert hasType(gamma[x1 := t1], e, t);
        }
        case Lam(x, tLam, e1) => {
            assert x1 != x && x1 !in FV(e1);
            // By definition: hasType(gamma, Lam(x, tLam, e1), t) == (exists t2 :: hasType(gamma[x := tLam], e1, t2)) && t == TypeVar
            var witness: bool :| (exists t2 :: hasType(gamma[x := tLam], e1, t2));
            // Now, pick some t2 such that hasType(gamma[x := tLam], e1, t2)
            // We use a ghost variable to pick t2
            ghost var t2: Type :| hasType(gamma[x := tLam], e1, t2);
            extendGamma(gamma[x := tLam], e1, t2, x1, t1);
            assert hasType((gamma[x := tLam])[x1 := t1], e1, t2);
            assert (gamma[x := tLam])[x1 := t1] == (gamma[x1 := t1])[x := tLam];
            assert hasType((gamma[x1 := t1])[x := tLam], e1, t2);
            assert (exists t2 :: hasType((gamma[x1 := t1])[x := tLam], e1, t2));
            assert hasType(gamma[x1 := t1], e, t);
        }
        case App(e1, e2) => {
            // hasType(gamma, App(e1, e2), t) == (exists t1', t2' :: hasType(gamma, e1, t1') && hasType(gamma, e2, t2') && t1' == TypeVar && t == t2')
            ghost var t1': Type;
            ghost var t2': Type;
            // Find witnesses for t1', t2'
            assert (exists t1', t2' :: hasType(gamma, e1, t1') && hasType(gamma, e2, t2') && t1' == TypeVar && t == t2');
            ghost var found: bool :| (exists t1', t2' :: hasType(gamma, e1, t1') && hasType(gamma, e2, t2') && t1' == TypeVar && t == t2');
            // Now, pick t1', t2' such that ...
            // Use a ghost variable to pick t1', t2'
            ghost var t1p: Type;
            ghost var t2p: Type;
            ghost var _witness: bool :| hasType(gamma, e1, t1p) && hasType(gamma, e2, t2p) && t1p == TypeVar && t == t2p;
            // x1 !in FV(App(e1, e2)) ==> x1 !in FV(e1) && x1 !in FV(e2)
            assert x1 !in FV(e1);
            assert x1 !in FV(e2);
            extendGamma(gamma, e1, t1p, x1, t1);
            extendGamma(gamma, e2, t2p, x1, t1);
            assert hasType(gamma[x1 := t1], e1, t1p);
            assert hasType(gamma[x1 := t1], e2, t2p);
            assert (exists t1', t2' :: hasType(gamma[x1 := t1], e1, t1') && hasType(gamma[x1 := t1], e2, t2') && t1' == TypeVar && t == t2');
            assert hasType(gamma[x1 := t1], e, t);
        }
        case Cond(e0, e1, e2) =>  {
            // hasType(gamma, Cond(e0, e1, e2), t) == hasType(gamma, e0, Bool) && hasType(gamma, e1, t) && hasType(gamma, e2, t)
            assert x1 !in FV(e0);
            assert x1 !in FV(e1);
            assert x1 !in FV(e2);
            extendGamma(gamma, e0, Bool, x1, t1);
            extendGamma(gamma, e1, t, x1, t1);
            extendGamma(gamma, e2, t, x1, t1);
            assert hasType(gamma[x1 := t1], e0, Bool);
            assert hasType(gamma[x1 := t1], e1, t);
            assert hasType(gamma[x1 := t1], e2, t);
            assert hasType(gamma[x1 := t1], e, t);
        }
    }
}    

function abs(a: real) : real {if a>0.0 then a else -a}
