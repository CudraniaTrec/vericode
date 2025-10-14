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
        assert expo(2, 0) == 1;
        assert expo(3, 0) == 1;
        assert (1 - 1) % 5 == 0;
    } else if (n == 1) {
        assert expo(2, 3 * 1) == expo(2, 3);
        assert expo(2, 3) == 8;
        assert expo(3, 1) == 3;
        assert (8 - 3) % 5 == 0;
    } else {
        Expon23(n - 1);

        // expo(2, 3*n) = expo(2, 3*(n-1) + 3) = expo(2, 3*(n-1)) * expo(2, 3)
        assert expo(2, 3 * n) == expo(2, 3 * (n - 1)) * expo(2, 3);
        // expo(2, 3) == 8
        assert expo(2, 3) == 8;
        // expo(3, n) = expo(3, n-1) * 3
        assert expo(3, n) == expo(3, n - 1) * 3;

        // By induction hypothesis:
        // (expo(2, 3*(n-1)) - expo(3, n-1)) % 5 == 0
        // So expo(2, 3*(n-1)) == expo(3, n-1) mod 5

        // Now, (expo(2, 3*n) - expo(3, n)) % 5
        // = (8 * expo(2, 3*(n-1)) - 3 * expo(3, n-1)) % 5
        // = (8 * expo(3, n-1) - 3 * expo(3, n-1)) % 5   [since expo(2, 3*(n-1)) == expo(3, n-1) mod 5]
        // = (5 * expo(3, n-1)) % 5 == 0

        // To help Dafny, we split the calculation and use the induction hypothesis directly:
        var a := expo(2, 3 * (n - 1));
        var b := expo(3, n - 1);
        assert (a - b) % 5 == 0; // induction hypothesis
        // So a % 5 == b % 5
        assert a % 5 == b % 5;

        // Now, compute (8*a - 3*b) % 5
        // 8 mod 5 = 3, so 8*a % 5 = 3*a % 5
        // (8*a - 3*b) % 5 == (3*a - 3*b) % 5 == 3*(a-b) % 5
        assert (8 * a - 3 * b) % 5 == (3 * (a - b)) % 5;

        // Since (a-b) % 5 == 0, 3*(a-b) % 5 == 0
        assert (3 * (a - b)) % 5 == 0;

        // So (expo(2, 3*n) - expo(3, n)) % 5 == 0
        assert (expo(2, 3 * n) - expo(3, n)) % 5 == 0;
    }
}

method check() {
}

function abs(a: real) : real {if a>0.0 then a else -a}
