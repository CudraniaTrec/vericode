
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
        invariant x == 5 ^ (|n - k|)
        invariant y == f2(n) - 5 ^ (|n - k|) * f2(k)
        invariant a == 0 // a is not assigned until after the loop
        decreases k
    {
        y := x*(k%4) + y;
        x := 5*x;
        k := k/3;
    }
    assert k == 0;
    assert x == 5 ^ (|n - 0|);
    assert y == f2(n) - 5 ^ (|n - 0|) * f2(0);
    assert f2(0) == 0;
    a := y;
}

function abs(a: real) : real {if a>0.0 then a else -a}
