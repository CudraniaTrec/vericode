method GetLucidNumbers(n: int) returns (lucids: seq<int>)
    ensures forall x :: 1 <= x <= n ==> (x in lucids <==> IsLucid(x))
    ensures lucids == [x | x := 1 .. n where IsLucid(x)]
{
    var buf := new seq<int>[];
    var isLucid := new bool[n+1];
    // 1 is always lucid
    if n >= 1 {
        isLucid[1] := true;
        buf := buf + [1];
    }

    var k := 2;
    while k * k <= n
        invariant 2 <= k <= n+1
        decreases n - k
    {
        var pow := k * k;
        while pow <= n
            invariant k*k <= pow <= n+1
            decreases n - pow
        {
            if !isLucid[pow] {
                isLucid[pow] := true;
                buf := buf + [pow];
            }
            pow := pow * k;
        }
        k := k + 1;
    }
    lucids := buf;
}

// Helper predicate for lucid numbers
predicate IsLucid(x: int)
{
    x == 1 || exists b: int, e: int :: b >= 2 && e >= 2 && x == b ^ e
}