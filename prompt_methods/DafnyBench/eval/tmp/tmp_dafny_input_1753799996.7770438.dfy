
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
        invariant y == 1 << (n - k)
        invariant x + y == f(n - k) + 2 * (f(n/2) - f((n-k)/2))
        invariant x + y == f(n - k) + (if (n - k) == 0 then 0 else 2*f((n-k)/2) - 1)
        invariant x + y == f(n - k) + 2*f((n-k)/2) - (if (n - k) == 0 then 0 else 1)
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
}

function abs(a: real) : real {if a>0.0 then a else -a}
