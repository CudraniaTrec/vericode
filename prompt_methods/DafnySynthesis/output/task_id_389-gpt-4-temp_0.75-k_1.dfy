method Lucas(n: nat) returns (l: nat)
    ensures l == if n == 0 then 2 else if n == 1 then 1 else Lucas(n - 1) + Lucas(n - 2)
{
    if n == 0 {
        return 2;
    } else if n == 1 {
        return 1;
    } else {
        var a := 2;
        var b := 1;
        var i := 2;
        while i <= n
            invariant 2 <= i <= n + 1
            invariant a == Lucas(i - 2)
            invariant b == Lucas(i - 1)
        {
            var temp := a + b;
            a := b;
            b := temp;
            i := i + 1;
        }
        return b;
    }
}