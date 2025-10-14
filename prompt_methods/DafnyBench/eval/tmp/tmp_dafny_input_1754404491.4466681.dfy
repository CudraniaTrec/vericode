
function Power(n:nat):nat 
{
    if n == 0 then 1 else 2 * Power(n-1)
}

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
    p := 2*n;
}

method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
{
    p:=1;
    var i:=0;
    while i!=n
        invariant 0 <= i <= n
        invariant p == Power(i)
    {
        p:= CalcPower(p);
        i:=i+1;
        assert p == 2 * Power(i-1);
        assert p == Power(i);
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
