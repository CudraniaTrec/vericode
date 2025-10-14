
ghost function pow(a: int, e: nat): int {
    if e == 0 then 1 else a*pow(a, e-1)
}

method Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
{

    var x:nat := 1;
    var k:nat := 0;
    while k < n
        invariant 0 <= k <= n
        invariant x == pow(a, k)
        decreases n - k
    {
        x := a*x;
         
        k := k + 1;

    }
    y := x;

}

function abs(a: real) : real {if a>0.0 then a else -a}
