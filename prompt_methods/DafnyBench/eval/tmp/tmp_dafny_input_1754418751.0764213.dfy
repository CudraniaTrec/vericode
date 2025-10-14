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
        assert expo(2, 3) == 8;
        assert expo(3, 1) == 3;
        assert (8 - 3) % 5 == 0;
    } else {
        Expon23(n - 1);
        // expo(2, 3*n) = expo(2, 3*(n-1)) * expo(2, 3)
        assert expo(2, 3 * n) == expo(2, 3 * (n - 1)) * expo(2, 3);
        assert expo(2, 3) == 8;
        assert expo(2, 3 * n) == expo(2, 3 * (n - 1)) * 8;
        assert expo(3, n) == expo(3, n - 1) * 3;
        // By induction hypothesis:
        assert ((expo(2, 3 * (n - 1)) - expo(3, n - 1)) % 5) == 0;
        // Let a == expo(2, 3*(n-1)), b == expo(3, n-1)
        var a := expo(2, 3 * (n - 1));
        var b := expo(3, n - 1);
        // a % 5 == b % 5 by induction hypothesis
        // So, a = b + 5*k for some integer k
        // expo(2, 3*n) - expo(3, n) = 8*a - 3*b
        // = 8*(b + 5*k) - 3*b = 8*b + 40*k - 3*b = 5*b + 40*k = 5*(b + 8*k)
        // which is divisible by 5
        assert (expo(2, 3 * n) - expo(3, n)) % 5 == ((8 * a - 3 * b) % 5);
        assert (8 * a - 3 * b) % 5 == ((8 % 5) * (a % 5) - (3 % 5) * (b % 5)) % 5;
        assert 8 % 5 == 3;
        assert 3 % 5 == 3;
        assert ((3 * (a % 5) - 3 * (b % 5)) % 5) == (3 * ((a % 5) - (b % 5))) % 5;
        assert (a % 5) == (b % 5);
        assert (3 * ((a % 5) - (b % 5))) % 5 == 0;
        assert (expo(2, 3 * n) - expo(3, n)) % 5 == 0;
    }
}

method check() {
}

function abs(a: real) : real {if a>0.0 then a else -a}
