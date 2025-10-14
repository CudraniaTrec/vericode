
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
    match m
        case Succ(Zero) => 
            // m = 1, Odd(1) holds, so n must also be odd
            // add(Succ(Zero), n) = Succ(add(Zero, n)) = Succ(n)
            // Even(Succ(n)) == Odd(n), but Odd(n) holds by precondition
            assert add(Succ(Zero), n) == Succ(n);
            assert Odd(n);
            assert Even(Succ(n));
        case Succ(Succ(m')) => 
            // m = Succ(Succ(m')), so m' is Nat
            // Odd(Succ(Succ(m'))) == Even(Succ(m')) == Odd(m')
            assert Odd(m');
            // Inductive step
            SumMNIsEven(m', n);
            // add(Succ(Succ(m')), n) = Succ(Succ(add(m', n)))
            // Even(Succ(Succ(add(m', n)))) == Even(add(m', n))
            // So, Even(add(m, n)) == Even(add(m', n)), which holds by induction
            assert Even(add(m, n)) == Even(add(m', n));
}

function abs(a: real) : real {if a>0.0 then a else -a}
