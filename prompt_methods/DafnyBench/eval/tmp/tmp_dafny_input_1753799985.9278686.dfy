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
        invariant x == exp(5, countSteps(n, k))
        invariant y + x * f2(k) == f2(n)
    {
        y := x*(k%4) + y;
        x := 5*x;
        k := k/3;
    }
    a := y;
}

// Helper function: exponentiation for natural numbers
function exp(b: nat, e: nat): nat
    decreases e
{
    if e == 0 then 1 else b * exp(b, e - 1)
}

// Helper function: counts how many times you can divide n by 3 before reaching k
function countSteps(n: nat, k: nat): nat
    decreases n
{
    if n == k then 0 else 1 + countSteps(n/3, k)
}

function abs(a: real) : real {if a>0.0 then a else -a}
