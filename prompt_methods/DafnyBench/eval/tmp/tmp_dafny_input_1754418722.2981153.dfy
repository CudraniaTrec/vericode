
// verifies
function expo(x:int, n:nat): int
requires n >= 0;
{
    if (n == 0) then 1
    else x * expo(x, n - 1)
}

lemma {:induction false} Expon23(n: nat)
requires n >= 0;
ensures ((expo(2, 3 * n) - expo(3, n))) % 5 == 0;
{
    if (n == 0) { 
        assert expo(2, 3 * 0) == 1;
        assert expo(3, 0) == 1;
        assert (1 - 1) % 5 == 0;
    } else if (n == 1) {
        assert expo(2, 3 * 1) == expo(2, 3);
        assert expo(2, 3) == 8;
        assert expo(3, 1) == 3;
        assert (8 - 3) % 5 == 0;
    } else {
        var i:nat := n;
        var j:nat := n;
        // assume true for n - 1
        // prove for n - 1
        Expon23(n - 1);
        // Inductive step:
        // expo(2, 3*n) = 8 * expo(2, 3*(n-1))
        // expo(3, n) = 3 * expo(3, n-1)
        assert expo(2, 3 * n) == expo(2, 3 * (n - 1) + 3);
        assert expo(2, 3 * (n - 1) + 3) == expo(2, 3) * expo(2, 3 * (n - 1));
        assert expo(2, 3) == 8;
        assert expo(2, 3 * n) == 8 * expo(2, 3 * (n - 1));
        assert expo(3, n) == 3 * expo(3, n - 1);
        // By induction hypothesis:
        assert ((expo(2, 3 * (n - 1)) - expo(3, n - 1)) % 5) == 0;
        // So expo(2, 3 * (n - 1)) == expo(3, n - 1) mod 5
        // Now, 8 * expo(2, 3 * (n - 1)) - 3 * expo(3, n - 1) == 8*a - 3*a = 5*a mod 5 == 0
        assert ((8 * expo(2, 3 * (n - 1)) - 3 * expo(3, n - 1)) % 5) == 0;
        assert ((expo(2, 3 * n) - expo(3, n)) % 5) == 0;
    }
}

method check() {
}

function abs(a: real) : real {if a>0.0 then a else -a}
