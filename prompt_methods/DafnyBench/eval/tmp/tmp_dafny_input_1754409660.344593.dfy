
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
    // Strongest induction on m
    match m
        case Succ(Zero) => 
            // m = 1, Odd(m) so m = Succ(Zero), so Even(m') where m' = Zero, so Odd(Succ(Zero)) = Even(Zero) = true
            // n is odd, so n = Succ(k) for some k, and Even(add(Succ(Zero), n)) = Even(Succ(add(Zero, n))) = Even(Succ(n)) = Odd(n)
            // But Odd(n) is true by precondition
            assert add(Succ(Zero), n) == Succ(add(Zero, n));
            assert add(Zero, n) == n;
            assert add(Succ(Zero), n) == Succ(n);
            assert Even(add(Succ(Zero), n)) == Odd(n);
            assert Odd(n);
        case Succ(Succ(m')) => 
            // m = Succ(Succ(m')), Odd(m) = Even(Succ(m')) = Odd(m')
            // n is odd
            // IH: Even(add(m', n)) under Odd(m'), Odd(n)
            // Show: Even(add(Succ(Succ(m')), n))
            // add(Succ(Succ(m')), n) = Succ(Succ(add(m', n)))
            // Even(Succ(Succ(add(m', n)))) = Odd(Succ(add(m', n))) = Even(add(m', n))
            // By IH, Even(add(m', n))
            assert Odd(m') by {
                // Odd(m) = Even(Succ(m')) = Odd(m')
                // So Odd(m') holds
            };
            SumMNIsEven(m', n);
            assert Even(add(m', n));
            assert add(Succ(Succ(m')), n) == Succ(Succ(add(m', n)));
            assert Even(add(Succ(Succ(m')), n)) == Odd(Succ(add(m', n)));
            assert Odd(Succ(add(m', n))) == Even(add(m', n));
            assert Even(add(Succ(Succ(m')), n));
}

function abs(a: real) : real {if a>0.0 then a else -a}
