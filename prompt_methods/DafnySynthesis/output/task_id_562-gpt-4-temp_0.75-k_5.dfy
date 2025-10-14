method LongestSublistLength(lists: seq<seq<int>>): nat
    // Returns the length of the longest sublist in 'lists'.
    // If 'lists' is empty, returns 0.
{
    var maxLen := 0;
    for i := 0 to |lists| - 1
        invariant 0 <= i <= |lists|
        invariant 0 <= maxLen <= (if |lists| == 0 then 0 else max(Seq#Max(lists, seq => |seq|), 0))
    {
        if |lists[i]| > maxLen {
            maxLen := |lists[i]|;
        }
    }
    return maxLen;
}