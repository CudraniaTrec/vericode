
module RussianMultiplication {
    
    export provides mult

    method mult(n0 : int, m0 : int) returns (res : int)
    ensures res == (n0 * m0);
    {
        var n, m : int;
        res := 0;
        if (n0 >= 0) {
            n,m := n0, m0;
        } 
        else {
            n,m := -n0, -m0;
        }
        while (0 < n)
            invariant 0 <= n <= if n0 >= 0 then n0 else -n0
            invariant res + n * m == (if n0 >= 0 then n0 else -n0) * m
            invariant m == (if n0 >= 0 then m0 else -m0)
        { 
            res := res + m; 
            n := n - 1; 
        }
        assert res == (if n0 >= 0 then n0 else -n0) * (if n0 >= 0 then m0 else -m0);
        assert res == n0 * m0;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
