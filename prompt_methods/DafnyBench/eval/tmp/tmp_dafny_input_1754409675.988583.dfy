
/*
HW1: Define over naturals (as an algebraic data type)  the predicates odd(x) and even(x) 
and prove that the addition of two odd numbers is an even number.
Deadline: Tuesday 12.10, 14:00
*/

datatype Nat = Zero | Succ(Pred: Nat)

function add(m: Nat, n: Nat) : Nat
{
    match m
        case Zero => n
        case Succ(m') => Succ(add(m', n))
}

predicate Odd(m: Nat)
{
    match m
        case Zero => false
        case Succ(m') => Even(m')
}


predicate Even(m: Nat)
{
    match m
        case Zero => true
        case Succ(m') => Odd(m')
}


lemma SumMNIsEven(m: Nat, n: Nat)
    requires Odd(m)
    requires Odd(n)
    ensures Even(add(m,n))
{
    // Induction on m
    match m
        case Zero =>
            // Impossible by precondition
            assert false;
        case Succ(m1) =>
            match m1
                case Zero =>
                    // m = Succ(Zero)
                    // Odd(Succ(Zero)) == Even(Zero) == true, so allowed
                    // n is odd
                    // add(Succ(Zero), n) == Succ(add(Zero, n)) == Succ(n)
                    // Even(Succ(n)) == Odd(n)
                    assert add(m, n) == Succ(n);
                    assert Even(add(m, n)) == Odd(n);
                    assert Odd(n);
                case Succ(m2) =>
                    // m = Succ(Succ(m2))
                    // Odd(m) = Even(Succ(m1)) = Odd(m1)
                    // So Odd(m1)
                    assert Odd(m1);
                    // Inductive hypothesis
                    SumMNIsEven(m1, n);
                    // add(m, n) == Succ(Succ(add(m2, n)))
                    assert add(m, n) == Succ(Succ(add(m2, n)));
                    // Even(Succ(Succ(x))) == Odd(Succ(x)) == Even(x)
                    assert Even(add(m, n)) == Even(add(m2, n));
                    // By IH, Even(add(m2, n))
                    assert Even(add(m, n));
}

function abs(a: real) : real {if a>0.0 then a else -a}
