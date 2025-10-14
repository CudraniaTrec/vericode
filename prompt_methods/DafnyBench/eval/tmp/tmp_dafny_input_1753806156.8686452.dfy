
lemma {:induction false} Divby2(n: nat)
ensures (n*(n-1))%2 == 0
{
    if n == 0 {
        assert (n*(n-1))%2 == 0;
    } else {
        // Strongest possible assertion before recursive call
        assert n > 0;
        Divby2(n - 1); // proved in case n - 1
        // Prove for n using the result for n-1
        assert ((n*(n-1))%2 == 0);
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
