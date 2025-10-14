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
        // expo(2, 3*n) = expo(2, 3*(n-1) + 3) = expo(2, 3*(n-1)) * expo(2, 3)
        assert expo(2, 3 * n) == expo(2, 3 * (n - 1)) * expo(2, 3);
        assert expo(2, 3) == 8;
        assert expo(2, 3 * n) == expo(2, 3 * (n - 1)) * 8;
        assert expo(3, n) == expo(3, n - 1) * 3;
        // By induction hypothesis:
        assert ((expo(2, 3 * (n - 1)) - expo(3, n - 1)) % 5) == 0;
        // Let k = expo(2, 3 * (n - 1)) = expo(3, n - 1) mod 5
        // So expo(2, 3 * n) - expo(3, n) = 8*k - 3*k = 5*k, which is divisible by 5
        var k := expo(2, 3 * (n - 1));
        var l := expo(3, n - 1);
        assert k % 5 == l % 5;
        assert (8 * k - 3 * l) % 5 == ((8 % 5) * (k % 5) - (3 % 5) * (l % 5)) % 5;
        assert 8 % 5 == 3;
        assert 3 % 5 == 3;
        assert (8 * k - 3 * l) % 5 == (3 * (k % 5) - 3 * (l % 5)) % 5;
        assert (3 * (k % 5) - 3 * (l % 5)) % 5 == (3 * ((k % 5) - (l % 5))) % 5;
        assert k % 5 == l % 5 ==> (k % 5) - (l % 5) == 0;
        assert (3 * ((k % 5) - (l % 5))) % 5 == 0;
        assert (expo(2, 3 * n) - expo(3, n)) % 5 == 0;
    }
}

method check() {
}

function abs(a: real) : real {if a>0.0 then a else -a}
