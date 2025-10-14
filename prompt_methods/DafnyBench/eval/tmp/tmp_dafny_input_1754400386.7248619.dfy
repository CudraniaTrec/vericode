
function fact (n:nat): nat
{if n == 0 then 1 else n * fact(n-1)}

function factAcc (n:nat, a:int): int
{if (n==0) then a else factAcc(n-1,n*a)}

function factAlt(n:nat):int
{factAcc(n,1)}

lemma factAcc_correct (n:nat, a:int)
 ensures factAcc(n, a) == a*fact(n)
{
    if n == 0 {
        // factAcc(0, a) == a, fact(0) == 1, so a*1 == a
        assert factAcc(0, a) == a;
        assert fact(0) == 1;
        assert a * fact(0) == a;
    } else {
        // factAcc(n, a) == factAcc(n-1, n*a)
        // By IH: factAcc(n-1, n*a) == n*a * fact(n-1)
        factAcc_correct(n-1, n*a);
        assert factAcc(n, a) == factAcc(n-1, n*a);
        assert factAcc(n-1, n*a) == n*a * fact(n-1);
        assert fact(n) == n * fact(n-1);
        assert n*a * fact(n-1) == a * (n * fact(n-1));
        assert a * (n * fact(n-1)) == a * fact(n);
        assert factAcc(n, a) == a * fact(n);
    }
}

lemma factAlt_correct (n:nat)
 ensures factAlt(n) == fact(n)
{
    factAcc_correct(n,1);
}

datatype List<T> = Nil | Cons(T, List<T>)

function length<T> (l: List<T>) : nat
{
    match l
    case Nil => 0
    case Cons(_, r) => 1 + length(r)
}

lemma {:induction false} length_non_neg<T> (l:List<T>)
    ensures length(l) >= 0
{
    match l
    case Nil =>
        assert length(l) == 0;
    case Cons(_, r) =>
        length_non_neg(r);
        assert length(l) == 1 + length(r);
        assert length(r) >= 0;
        assert 1 + length(r) >= 0;
}

function lengthTL<T> (l: List<T>, acc: nat) : nat
{
    match l
    case Nil => acc
    case Cons(_, r) => lengthTL(r, 1 + acc)
}

lemma {:induction false}lengthTL_aux<T> (l: List<T>, acc: nat)
    ensures lengthTL(l, acc) == acc + length(l)
{
    match l
    case Nil => 
        assert lengthTL(l, acc) == acc;
        assert length<T>(Nil) == 0;
        assert acc + length<T>(Nil) == acc;
    case Cons(_, r) =>
        lengthTL_aux(r, acc + 1);
        assert lengthTL(l, acc) == lengthTL(r, acc + 1);
        assert lengthTL(r, acc + 1) == (acc + 1) + length(r);
        assert length(l) == 1 + length(r);
        assert (acc + 1) + length(r) == acc + (1 + length(r));
        assert acc + (1 + length(r)) == acc + length(l);
}

lemma lengthEq<T> (l: List<T>)
    ensures length(l) == lengthTL(l,0)
{
    lengthTL_aux(l, 0);
}

function abs(a: real) : real {if a>0.0 then a else -a}
