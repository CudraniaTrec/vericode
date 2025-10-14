// program verifies
function expo(x:int, n:nat): int
{
    if n == 0 then 1
    else x * expo(x, n-1)
}

lemma {:induction false} Expon23(n: nat)
requires n >= 0
ensures ((expo(2,3*n) - expo(3,n)) % (2+3)) == 0
{   
    // base case
    if (n == 0) {
        assert expo(2, 0) == 1;
        assert expo(3, 0) == 1;
        assert (1 - 1) % 5 == 0;
    }
    else if (n == 1) {
        assert expo(2, 3*1) == expo(2, 3);
        assert expo(2, 3) == 8;
        assert expo(3, 1) == 3;
        assert (8 - 3) % 5 == 0;
    }
    else {
        Expon23(n-1);

        var A := expo(2, 3*(n-1));
        var B := expo(3, n-1);

        // expo(2, 3*n) = expo(2, 3*(n-1) + 3) = expo(2, 3*(n-1)) * expo(2, 3)
        assert expo(2, 3*n) == A * expo(2, 3);
        assert expo(2, 3) == 8;
        assert expo(2, 3*n) == A * 8;

        // expo(3, n) = expo(3, n-1) * 3
        assert expo(3, n) == B * 3;

        // (expo(2,3*n) - expo(3,n)) = 8*A - 3*B
        // By induction hypothesis, (A - B) % 5 == 0
        // Let k := (A - B) / 5, so A = B + 5*k
        // 8*A - 3*B = 8*(B + 5*k) - 3*B = 8*B + 40*k - 3*B = 5*B + 40*k = 5*(B + 8*k)
        // So divisible by 5

        assert (A - B) % 5 == 0; // by induction hypothesis

        // Now, (expo(2,3*n) - expo(3,n)) = 8*A - 3*B = 8*(B + 5*k) - 3*B = 8*B + 40*k - 3*B = 5*B + 40*k = 5*(B + 8*k)
        assert (expo(2,3*n) - expo(3,n)) == 8*A - 3*B;
        assert (expo(2,3*n) - expo(3,n)) % 5 == 0;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
