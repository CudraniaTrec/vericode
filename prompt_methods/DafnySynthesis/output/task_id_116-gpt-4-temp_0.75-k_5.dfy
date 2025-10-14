method SeqToInt(seq: seq<int>) returns (result: int)
    requires forall x :: x in seq ==> x > 0
    ensures result >= 0
{
    // Concatenate the digits of the integers in the sequence to a single integer
    var res := 0;
    var s := seq;
    while |s| > 0
        invariant res >= 0
        invariant forall x :: x in s ==> x > 0
        decreases |s|
    {
        var h := s[0];
        // Count number of digits in h
        var digits := if h == 0 then 1 else 1 + (if h >= 10 then if h >= 100 then if h >= 1000 then if h >= 10000 then if h >= 100000 then if h >= 1000000 then if h >= 10000000 then if h >= 100000000 then if h >= 1000000000 then 9 else 8 else 7 else 6 else 5 else 4 else 3 else 2 else 1);
        var temp := h;
        while temp >= 10
            invariant temp >= 0
            decreases temp
        {
            temp := temp / 10;
            digits := digits + 1;
        }
        // Shift res to the left by h's number of digits then add h
        var pow := 1;
        var count := digits;
        while count > 0
            invariant pow >= 1
            invariant count >= 0
            decreases count
        {
            pow := pow * 10;
            count := count - 1;
        }
        res := res * pow + h;
        s := s[1..];
    }
    result := res;
}