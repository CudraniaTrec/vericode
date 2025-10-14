
datatype Nat = Zero | Succ(Pred: Nat)

/*

Nat: Zero, Succ(Zero), Succ(Succ(Zero)), ...

*/

lemma Disc(n: Nat)
ensures n.Succ? || n.Zero?
{
    match n
    case Zero => assert n.Zero?;
    case Succ(_) => assert n.Succ?;
}

lemma LPred(n: Nat)
ensures Succ(n).Pred == n
{
    assert Succ(n).Pred == n;
}

// Succ(m') > m'

function add(m: Nat, n: Nat) : Nat
{
    match m
    case Zero => n
    case Succ(m') => Succ(add(m', n))
}

// add(m, Zero) = m

lemma AddZero(m: Nat)
ensures add(m, Zero) == m
{
    match m
    case Zero => assert add(Zero, Zero) == Zero;
    case Succ(m') => 
        AddZero(m');
        assert add(Succ(m'), Zero) == Succ(add(m', Zero));
        assert add(Succ(m'), Zero) == Succ(m');
}

lemma AddAssoc(m: Nat, n: Nat, p: Nat)
ensures add(m, add(n, p)) == add(add(m, n), p)
{
    match m
    case Zero => assert add(Zero, add(n, p)) == add(n, p) && add(add(Zero, n), p) == add(n, p);
    case Succ(m') => 
        AddAssoc(m', n, p);
        assert add(Succ(m'), add(n, p)) == Succ(add(m', add(n, p)));
        assert add(add(Succ(m'), n), p) == add(Succ(add(m', n)), p);
        assert add(Succ(add(m', n)), p) == Succ(add(add(m', n), p));
        assert Succ(add(m', add(n, p))) == Succ(add(add(m', n), p));
}

lemma AddComm(m: Nat, n: Nat)
ensures add(m, n) == add(n, m)
{
    match m
    case Zero => AddZero(n);
    case Succ(m') => 
        AddComm(m', n);
        assert add(Succ(m'), n) == Succ(add(m', n));
        assert add(n, Succ(m')) == Succ(add(n, m'));
        AddComm(n, m');
        assert add(m', n) == add(n, m');
        assert Succ(add(m', n)) == Succ(add(n, m'));
}

predicate lt(m: Nat, n: Nat)
{
    (m.Zero? && n.Succ?) ||
    (m.Succ? && n.Succ? && lt(m.Pred, n.Pred))
}

lemma Test1(n:Nat)
ensures lt(n, Succ(Succ(n)))
{
    // lt(n, Succ(Succ(n))) holds for all n
    match n
    case Zero => assert lt(Zero, Succ(Succ(Zero)));
    case Succ(n') => 
        Test1(n');
        assert lt(n, Succ(Succ(n)));
}

lemma Test2(n: Nat)
ensures n < Succ(n)
{
    match n
    case Zero => assert lt(Zero, Succ(Zero));
    case Succ(n') => 
        Test2(n');
        assert lt(Succ(n'), Succ(Succ(n')));
}

lemma LtTrans(m: Nat, n: Nat, p: Nat)
requires lt(m, n)
requires lt(n, p)
ensures lt(m, p)
{
    // Strongest induction on m and n
    if m.Zero? && n.Succ? {
        // m = Zero, n = Succ(n0)
        if p.Succ? {
            // p = Succ(p0)
            assert lt(Zero, p);
        } else {
            // p = Zero, contradiction: lt(n, p) cannot hold
            assert false;
        }
    } else if m.Succ? && n.Succ? {
        // m = Succ(m'), n = Succ(n')
        LtTrans(m.Pred, n.Pred, p.Pred);
        if p.Succ? {
            assert lt(m.Pred, p.Pred);
            assert lt(Succ(m.Pred), Succ(p.Pred));
        } else {
            // p = Zero, contradiction: lt(n, p) cannot hold
            assert false;
        }
    } else {
        // m.Zero? && n.Zero? or m.Succ? && n.Zero?
        // But lt(m, n) cannot hold in these cases
        assert false;
    }
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

lemma Disc2<T>(l: List<T>, a: T)
ensures Cons(a, l).head == a && Cons(a, l).tail == l
{
    assert Cons(a, l).head == a;
    assert Cons(a, l).tail == l;
}

function size<T>(l: List<T>): nat
{
    match l
    case Nil => 0
    case Cons(x, l') => size<T>(l') + 1
}

function app<T>(l1: List<T>, l2: List<T>) : List<T>
{
    match l1
    case Nil => l2
    case Cons(x, l1') => Cons(x, app(l1', l2))
}

lemma LenApp<T>(l1: List<T>, l2: List<T>)
ensures size(app(l1, l2)) == size(l1) + size(l2)
{
    match l1
    case Nil => assert size(app(Nil, l2)) == size(l2) && size(Nil) + size(l2) == size(l2);
    case Cons(x, l1') => 
        LenApp(l1', l2);
        assert size(app(Cons(x, l1'), l2)) == size(app(l1', l2)) + 1;
        assert size(Cons(x, l1')) + size(l2) == size(l1') + 1 + size(l2);
        assert size(app(l1', l2)) == size(l1') + size(l2);
        assert size(app(Cons(x, l1'), l2)) == size(l1') + size(l2) + 1;
}

function rev<T> (l: List<T>) : List<T>
{
    match l
    case Nil => Nil
    case Cons(x, l') => app(rev(l'), Cons(x, Nil))
}

lemma AppNil<T>(l: List<T>)
ensures app(l, Nil) == l
{
    match l
    case Nil => assert app(Nil, Nil) == Nil;
    case Cons(x, l') => 
        AppNil(l');
        assert app(Cons(x, l'), Nil) == Cons(x, app(l', Nil));
        assert app(l', Nil) == l';
        assert Cons(x, l') == Cons(x, l');
}

lemma LR1<T> (l: List<T>, x: T)
ensures rev(app(l, Cons(x, Nil))) == Cons(x, rev(l))
{
    match l
    case Nil => assert rev(app(Nil, Cons(x, Nil))) == rev(Cons(x, Nil)) && rev(Cons(x, Nil)) == Cons(x, Nil);
    case Cons(y, l') => 
        LR1(l', x);
        assert rev(app(Cons(y, l'), Cons(x, Nil))) == app(rev(app(l', Cons(x, Nil))), Cons(y, Nil));
        assert rev(app(l', Cons(x, Nil))) == Cons(x, rev(l'));
        assert app(Cons(x, rev(l')), Cons(y, Nil)) == Cons(y, app(Cons(x, rev(l')), Nil));
        assert app(Cons(x, rev(l')), Nil) == Cons(x, rev(l'));
        assert Cons(y, Cons(x, rev(l'))) == Cons(y, Cons(x, rev(l')));
        assert Cons(y, app(Cons(x, rev(l')), Nil)) == Cons(y, Cons(x, rev(l')));
}

lemma RevRev<T>(l: List<T>)
ensures rev(rev(l)) == l
{
    match l
    case Nil => assert rev(rev(Nil)) == Nil;
    case Cons(x, l') => {
        RevRev(l');
        LR1(rev(l'), x);
        assert rev(rev(Cons(x, l'))) == rev(app(rev(l'), Cons(x, Nil)));
        assert rev(app(rev(l'), Cons(x, Nil))) == Cons(x, rev(rev(l')));
        assert rev(rev(l')) == l';
        assert Cons(x, l') == Cons(x, l');
    }
}

/*
HW1: Define over naturals (as an algebraic data type)  the predicates odd(x) and even(x) 
and prove that the addition of two odd numbers is an even number.
Deadline: Tuesday 12.10, 14:00
*/

predicate even(n: Nat)
{
    n.Zero? || (n.Succ? && n.Pred.Succ? && even(n.Pred.Pred))
}

predicate odd(n: Nat)
{
    n.Succ? && (n.Pred.Zero? || (n.Pred.Succ? && odd(n.Pred.Pred)))
}

lemma OddPlusOddEven(m: Nat, n: Nat)
requires odd(m) && odd(n)
ensures even(add(m, n))
{
    // Strongest induction on m
    match m
    case Succ(m1) => 
        if m1.Zero? {
            // m = Succ(Zero), i.e., 1
            match n
            case Succ(n1) => 
                if n1.Zero? {
                    // n = Succ(Zero), i.e., 1
                    assert add(Succ(Zero), Succ(Zero)) == Succ(Succ(Zero));
                    assert even(Succ(Succ(Zero)));
                } else {
                    // n = Succ(Succ(n2)), n1 = Succ(n2)
                    OddPlusOddEven(Succ(Zero), n1.Pred);
                    assert odd(n1.Pred);
                    assert add(Succ(Zero), Succ(n1)) == Succ(Succ(n1));
                    assert even(Succ(Succ(n1)));
                }
            case Zero => assert false;
        } else {
            // m = Succ(Succ(m2)), m1 = Succ(m2)
            OddPlusOddEven(m1.Pred, n);
            assert odd(m1.Pred);
            assert add(Succ(m1), n) == Succ(add(m1, n));
            assert add(m1, n) == Succ(add(m1.Pred, n));
            assert even(add(Succ(m1), n)) == even(Succ(add(m1, n)));
            assert even(Succ(add(m1, n))) == even(Succ(Succ(add(m1.Pred, n))));
            assert even(Succ(Succ(add(m1.Pred, n))));
        }
    case Zero => assert false;
}

function abs(a: real) : real {if a>0.0 then a else -a}
