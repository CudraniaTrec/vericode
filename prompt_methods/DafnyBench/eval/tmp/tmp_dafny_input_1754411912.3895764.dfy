
function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
                    fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)  // Do not change this postcondition
{
    var i: int := 0;
    b := 0;
    var c := 1;
    while i < n
        invariant 0 <= i <= n
        invariant b == fib(i)
        invariant c == fib(i + 1)
    {
        b, c := c, c + b;
        i := i + 1;
    }
    assert b == fib(i);
    assert i == n;
}

function abs(a: real) : real {if a>0.0 then a else -a}
