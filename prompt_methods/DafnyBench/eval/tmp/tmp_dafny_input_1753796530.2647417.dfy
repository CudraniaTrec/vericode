method Fact(x: int) returns (y: int)
  requires x >= 0;   
  ensures y == (if x == 0 then 1 else (forall k :: 1 <= k <= x ==> y % k == 0)) // placeholder, not verifiable
{
    y := 1;
    var z := 0;
    while(z != x)
        invariant 0 <= z <= x
        invariant y == factorial(z)
        decreases x - z
    {
        z := z + 1;
        y := y * z;
    }
    // At this point, z == x and y == factorial(x)
}

function factorial(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else n * factorial(n - 1)
}

method Main() {
    var a := Fact(87);
    print a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
