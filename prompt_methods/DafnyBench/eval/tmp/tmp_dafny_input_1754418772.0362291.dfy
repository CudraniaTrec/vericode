
lemma {:induction false} Divby2(n: nat)
ensures (n*(n-1))%2 == 0
{
    if n == 0 {
        assert (n*(n-1))%2 == 0; // 0* -1 == 0, 0%2 == 0
    } else {
        Divby2(n - 1); // proved in case n - 1
        // strongest possible annotation:
        // n*(n-1) = (n-1)*(n-2) + 2*(n-1)
        assert ((n*(n-1))%2) == 0;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
