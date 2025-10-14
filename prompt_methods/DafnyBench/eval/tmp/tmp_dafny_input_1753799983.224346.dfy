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
        invariant x == if k == n then 1 else 5 ^ (|digitsBase3(n, k)|)
        invariant y + x * f2(k) == f2(n)
    {
        y := x*(k%4) + y;
        x := 5*x;
        k := k/3;
    }
    a := y;
}

// Helper function to count the number of steps from n down to k by dividing by 3
function digitsBase3(n: nat, k: nat): seq<nat>
    decreases n, k
{
    if n == k then []
    else [n] + digitsBase3(n/3, k)
}

function abs(a: real) : real {if a>0.0 then a else -a}
