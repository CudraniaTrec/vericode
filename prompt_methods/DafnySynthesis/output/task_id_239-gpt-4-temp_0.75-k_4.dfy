method CountSequences(m: int, n: int) returns (count: int)
    requires m > 0 && n > 0
    ensures count >= 0
{
    method Helper(prev: int, length: int) returns (res: int)
        requires prev >= 0
        requires length >= 0
        ensures res >= 0
    {
        if length == 0 {
            res := 1;
            return;
        }
        res := 0;
        var start := if prev == 0 then 1 else 2 * prev;
        var i := start;
        while i <= m
            invariant i >= start && i <= m + 1
            invariant res >= 0
        {
            var temp := Helper(i, length - 1);
            res := res + temp;
            i := i + 1;
        }
    }
    count := Helper(0, n);
}