
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
        Expon23(n-1); // lemma proved for case n-1  

        // training dafny up
        assert expo(2, 3*n) == expo(2, 3*(n-1) + 3);
        assert expo(2, 3*n) == expo(2, 3*(n-1)) * expo(2, 3);

        // training dafny up
        assert expo(2, 3) == 8;
        assert expo(2, 3*n) == expo(2, 3*(n-1)) * 8;

        // some more training
        assert expo(3, n) == expo(3, n-1) * 3;

        // not really needed
        var A := expo(2, 3*(n-1));
        var B := expo(3, n-1);
        assert ((A - B) % 5) == 0 by {
            assert ((expo(2, 3*(n-1)) - expo(3, n-1)) % 5) == 0;
        };

        // Now, show ((expo(2,3*n) - expo(3,n)) % 5) == 0
        // expo(2,3*n) - expo(3,n) = 8*A - 3*B
        // But A - B == 5*k for some k
        // 8*A - 3*B = 8*A - 8*B + 8*B - 3*B = 8*(A-B) + 5*B
        // So (8*(A-B) + 5*B) % 5 == 0
        assert (expo(2,3*n) - expo(3,n)) == 8*(A - B) + 5*B;
        assert ((expo(2,3*n) - expo(3,n)) % 5) == ((8*(A-B)) % 5 + (5*B) % 5) % 5;
        assert (8*(A-B)) % 5 == (3*(A-B)) % 5; // since 8 mod 5 = 3
        assert (5*B) % 5 == 0;
        assert ((expo(2,3*n) - expo(3,n)) % 5) == (3*(A-B)) % 5;
        assert (A-B) % 5 == 0;
        assert (3*(A-B)) % 5 == 0;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
