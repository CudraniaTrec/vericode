method Fact(x: int) returns (y: int)
  requires x >= 0;   
{
    y := 1;
    var z := 0;
    while(z != x)
        invariant 0 <= z <= x
        invariant y == if z == 0 then 1 else (forall k :: 1 <= k <= z ==> y % k == 0)
        invariant y == if z == 0 then 1 else (forall k :: 1 <= k <= z ==> y >= k)
        invariant y == if z == 0 then 1 else y == (if z == 0 then 1 else (1 * 2 * ... * z))
        decreases x - z
    {
        z := z + 1;
        y := y * z;
    }
    assert y == (if x == 0 then 1 else (1 * 2 * ... * x)); // For clarity, but not verifiable by Dafny
}
method Main() {
    var a := Fact(87);
    print a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
