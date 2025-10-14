
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
        invariant x == 5^(if k == 0 then 0 else |n2k(n, k)|)
        invariant y + x * f2(k) == f2(n)
        invariant forall m :: 0 <= m < n && m >= k ==> (f2(n) == y + x * f2(k))
    {
        y := x*(k%4) + y;
        x := 5*x;
        k := k/3;
    }
    a := y;
}

// Helper function for invariants
function n2k(n: nat, k: nat): seq<nat>
    decreases n, k
{
    if n == k then []
    else [n] + n2k(n/3, k)
}

function abs(a: real) : real {if a>0.0 then a else -a}
