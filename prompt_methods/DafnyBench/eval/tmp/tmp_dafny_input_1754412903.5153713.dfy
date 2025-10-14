ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

function pow5(e: nat): nat
    decreases e
{
    if e == 0 then 1 else 5 * pow5(e - 1)
}

function log3(n: nat): nat
    decreases n
{
    if n == 0 then 0 else 1 + log3(n/3)
}

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{

    var x:nat := 1;
    var y:nat := 0;
    var k:nat := n;
    var steps:nat := 0;
    while k > 0
        invariant 0 <= k <= n
        invariant x == pow5(steps)
        invariant y == f2(n) - x * f2(k)
        invariant steps == log3(n) - log3(k)
        decreases k
    {
        y := x*(k%4) + y;
        x := 5*x;
        k := k/3;
        steps := steps + 1;
    }
    assert k == 0;
    assert f2(0) == 0;
    assert steps == log3(n);
    assert x == pow5(steps);
    assert y == f2(n) - x * f2(0);
    a := y;
}

function abs(a: real) : real {if a>0.0 then a else -a}
