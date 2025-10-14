
function exp(x:int, e:int):int
	requires e >= 0
    ensures x > 0 ==> exp(x,e) > 0
{
    if e == 0 then 1 else x*exp(x,e-1)
}

lemma   exp3_Lemma(n:int) 
    requires n >= 1
	ensures (exp(3,n)-1)%2 == 0
{
    // Proof by induction on n
    if n == 1 {
        assert exp(3,1) == 3;
        assert (exp(3,1)-1) % 2 == (3-1)%2 == 2%2 == 0;
    } else {
        exp3_Lemma(n-1);
        assert exp(3,n) == 3 * exp(3, n-1);
        assert (exp(3,n)-1) % 2 == (3*exp(3,n-1)-1)%2;
        // Since exp(3,n-1) is odd (by induction), 3*odd = odd, odd-1 = even
        // So (exp(3,n)-1)%2 == 0
    }
}

lemma  mult8_Lemma(n:int)
	requires n >= 1
	ensures (exp(3,2*n) - 1)%8 == 0
{
    if(n==1){
        assert exp(3,2*1) == exp(3,2) == 9;
        assert (exp(3,2*1) - 1) % 8 == (9-1)%8 == 8%8 == 0;
    }
    else{
        // Inductive step
        // exp(3,2*n) = exp(3,2*(n-1)+2) = exp(3,2*(n-1)) * 9
        calc =={
            (exp(3,2*n) -1) % 8;
            == { assert exp(3,2*n) == exp(3,2*(n-1)) * 9; }
            (exp(3,2*(n-1)) * 9 - 1) % 8;
            == { assert (a:int) * 9 - 1 == (a*8 + a - 1); }
            (exp(3,2*(n-1)) * 8 + exp(3,2*(n-1)) - 1) % 8;
            == { mult8_Lemma(n-1); }
            (exp(3,2*(n-1)) - 1) % 8;
            == { assert (exp(3,2*(n-1)) - 1) % 8 == 0; }
            0;
        }
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
