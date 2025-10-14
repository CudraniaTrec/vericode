method CountSequences(m: int, n: int) returns (count: int)
    requires m > 0 && n > 0
    ensures count >= 0
{
    // Helper function: sequences starting with prev, length rem
    function method CountFrom(prev: int, rem: int): int
        requires prev >= 1
        requires rem >= 0
        decreases rem, m - prev
    {
        if rem == 0 then
            1
        else
            var total := 0;
            // next element x: 2*prev <= x <= m
            var lo := 2 * prev;
            if lo > m then 0
            else
                total := SumSequences(lo, m, rem)
            total
    }

    // Sum CountFrom(x, rem) for all x in [lo..hi]
    function method SumSequences(lo: int, hi: int, rem: int): int
        requires 1 <= lo && lo <= hi+1
        requires rem >= 0
        decreases hi - lo + 1, rem
    {
        if lo > hi then 0
        else CountFrom(lo, rem - 1) + SumSequences(lo + 1, hi, rem)
    }

    count := 0;
    // The first element x: 1 <= x <= m
    // For each possible first element, count sequences of length n-1
    // starting from x
    for x := 1 to m
        invariant 1 <= x <= m+1
        invariant count >= 0
    {
        count := count + CountFrom(x, n - 1);
    }
}