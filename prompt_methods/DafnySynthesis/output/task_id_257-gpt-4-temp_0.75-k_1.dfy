method SwapToSequence(a: int, b: int) returns (s: seq<int>)
        ensures s == [b, a]
    {
        s := [b, a];
    }