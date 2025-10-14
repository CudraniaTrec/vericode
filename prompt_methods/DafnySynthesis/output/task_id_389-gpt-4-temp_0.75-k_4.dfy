method Lucas(n: nat) returns (res: nat)
    ensures res == if n == 0 then 2 else if n == 1 then 1 else Lucas(n - 1) + Lucas(n - 2)
{
    if n == 0 {
        res := 2;
    } else if n == 1 {
        res := 1;
    } else {
        var a := 2;
        var b := 1;
        var i := 2;
        while i <= n
            invariant 2 <= i <= n + 1
            invariant a == Lucas(i - 2)
            invariant b == Lucas(i - 1)
        {
            var next := a + b;
            a := b;
            b := next;
            i := i + 1;
        }
        res := b;
    }
}

// Helper function for specification
function Lucas(n: nat): nat
{
    if n == 0 then 2
    else if n == 1 then 1
    else Lucas(n - 1) + Lucas(n - 2)
}