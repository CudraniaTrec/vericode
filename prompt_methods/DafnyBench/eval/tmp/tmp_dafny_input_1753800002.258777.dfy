ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

method mod(n:nat) returns (a:nat) 
ensures a == f(n)
{

    var x:nat := 0;
    var y:nat := 1;
    var k:nat := n;
    while k > 0
        invariant 0 <= k <= n
        invariant y == if n - k >= 0 then exp(2, n - k) else 0
        invariant x + y == f(n - k)
        decreases k
    {
        if (k%2 == 0) {
            x := x + y;
        } else {
        }
        y := 2*y;
        k := k/2;
    }
    a := x+y;
    assert a == f(n);
}

// Helper function for exponentiation
function exp(base: nat, power: nat): nat
{
    if power == 0 then 1 else base * exp(base, power - 1)
}
function abs(a: real) : real {if a>0.0 then a else -a}
