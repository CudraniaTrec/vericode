
//Problem 01
method sumOdds(n: nat) returns (sum: nat)
    requires n > 0;
    ensures sum == n * n;
{
    sum := 1;
    var i := 0;

    while i < n-1
        invariant 0 <= i <= n-1;
        invariant sum == (i+1)*(i+1);
    {
        i := i + 1;
        sum := sum + 2 * i + 1;
        assert sum == (i+1)*(i+1);
    }
}


//problem02
//a)
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 

//b)c)

method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{
    q := 0;
    r := n;
    while r >= d
        invariant 0 <= q <= n/2;
        invariant r == n - d*q;
        invariant r >= 0;
    {
        r := r - d;
        q := q + 1;
        assert r == n - d*q;
    } 
    assert (d*q) + r == n;
    assert 0 <= q <= n/2;
    assert 0 <= r < d;
}

function abs(a: real) : real {if a>0.0 then a else -a}
