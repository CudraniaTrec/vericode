function exp(x:int, e:int):int
    requires e >= 0
    ensures x > 0 ==> exp(x,e) > 0
{
    if e == 0 then 1 else x*exp(x,e-1)
}

lemma exp3_Lemma(n:int) 
    requires n >= 1
    ensures (exp(3,n)-1)%2 == 0
{
    if n == 1 {
        assert exp(3,1) == 3;
        assert (exp(3,1)-1) % 2 == 2 % 2 == 0;
    } else {
        exp3_Lemma(n-1);
        // Inductive hypothesis: (exp(3, n-1)-1)%2 == 0
        // So exp(3, n-1) is odd
        // exp(3, n) = 3 * exp(3, n-1)
        // (exp(3, n) - 1) = 3*exp(3, n-1) - 1
        // If exp(3, n-1) is odd, 3*odd is odd, odd-1 is even
        assert exp(3, n-1) % 2 == 1;
        assert (3 * exp(3, n-1)) % 2 == 1;
        assert (exp(3, n) - 1) % 2 == (3 * exp(3, n-1) - 1) % 2;
        assert (3 * exp(3, n-1) - 1) % 2 == 0;
    }
}

lemma mult8_Lemma(n:int)
    requires n >= 1
    ensures (exp(3,2*n) - 1)%8 == 0
{
    if n == 1 {
        assert exp(3,2*1) == exp(3,2) == 9;
        assert (9-1)%8 == 8%8 == 0;
    } else {
        mult8_Lemma(n-1);
        // exp(3,2*n) = exp(3,2*(n-1)+2) = exp(3,2*(n-1))*exp(3,2)
        // exp(3,2) = 9
        // So exp(3,2*n) = exp(3,2*(n-1))*9
        // (exp(3,2*n)-1) = 9*exp(3,2*(n-1)) - 1 = 8*exp(3,2*(n-1)) + (exp(3,2*(n-1))-1)
        assert exp(3,2*n) == exp(3,2*(n-1))*9;
        assert (exp(3,2*n)-1) == 8*exp(3,2*(n-1)) + (exp(3,2*(n-1))-1);
        assert (exp(3,2*n)-1)%8 == (8*exp(3,2*(n-1)) + (exp(3,2*(n-1))-1))%8;
        assert (8*exp(3,2*(n-1)))%8 == 0;
        assert (exp(3,2*n)-1)%8 == (exp(3,2*(n-1))-1)%8;
        // By induction hypothesis, (exp(3,2*(n-1))-1)%8 == 0
        assert (exp(3,2*n)-1)%8 == 0;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
