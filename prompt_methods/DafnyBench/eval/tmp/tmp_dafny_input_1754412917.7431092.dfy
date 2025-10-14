ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

function exp(b: nat, e: nat): nat
    decreases e
{
    if e == 0 then 1 else b * exp(b, e-1)
}

method mod(n:nat) returns (a:nat) 
ensures a == f(n)
{

    var x:nat := 0;
    var y:nat := 1;
    var k:nat := n;
    while k > 0
        invariant 0 <= k <= n
        invariant y == exp(2, n - k)
        invariant x + y == f(n - k)
    {
        if (k%2 == 0) {
            x := x + y;
            assert x + y == (x - y) + 2*y;
            assert (x - y) + 2*y + 2*y == f(n - k + 1);
        } else {
            assert x + y == f(n - k);
        }
        y := 2*y;
        k := k/2;
    }
    a := x+y;
    assert a == f(n);
}
function abs(a: real) : real {if a>0.0 then a else -a}
