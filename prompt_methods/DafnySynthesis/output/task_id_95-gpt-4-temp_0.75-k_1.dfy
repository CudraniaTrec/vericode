method MinListLength(lists: seq<seq<int>>) returns (minLen: int)
    ensures minLen == (if |lists| == 0 then 0 else min set { |lst| | lst in lists })
{
    if |lists| == 0 {
        minLen := 0;
    } else {
        var currMin := |lists[0]|;
        var i := 1;
        while i < |lists|
            invariant 1 <= |lists|
            invariant 0 <= i <= |lists|
            invariant currMin == min set { |lists[j]| | 0 <= j < i }
        {
            if |lists[i]| < currMin {
                currMin := |lists[i]|;
            }
            i := i + 1;
        }
        minLen := currMin;
    }
}