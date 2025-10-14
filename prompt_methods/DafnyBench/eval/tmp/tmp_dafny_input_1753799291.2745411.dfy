
function Fat(n:nat):nat
{
    if n == 0 then 1 else n*Fat(n-1)
}

method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
    f := 1;
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant f == Fat(i-1)
        decreases n - i + 1
    {
        f := f * i;
        i := i + 1;
    }
    return f;
}

function abs(a: real) : real {if a>0.0 then a else -a}
