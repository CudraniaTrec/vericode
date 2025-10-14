ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{

    var x:nat := 1;
    var y:nat := 0;
    var k:nat := n;
    while k > 0
        invariant 0 <= k <= n
        invariant x == if k == n then 1 else 5 ^ (log3(n) - log3(k))
        invariant y == f2(n) - x * f2(k)
        decreases k
    {
        y := x*(k%4) + y;
        x := 5*x;
        k := k/3;
    }
    assert k == 0;
    assert f2(0) == 0;
    a := y;
}

// Helper function to compute the number of times n can be divided by 3 before reaching 0
function log3(n: nat): nat
    decreases n
{
    if n == 0 then 0 else 1 + log3(n/3)
}

function abs(a: real) : real {if a>0.0 then a else -a}
