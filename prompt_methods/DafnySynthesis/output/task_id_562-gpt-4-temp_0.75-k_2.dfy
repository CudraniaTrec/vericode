//Dafny Code

method LongestSublistLength(lists: seq<seq<int>>): int
    ensures forall s: seq<int> :: s in lists ==> |s| <= LongestSublistLength(lists)
    ensures exists s: seq<int> :: s in lists && |s| == LongestSublistLength(lists) || lists == []
{
    var maxLen := 0;
    var i := 0;
    while i < |lists|
        invariant 0 <= i <= |lists|
        invariant forall j :: 0 <= j < i ==> |lists[j]| <= maxLen
        invariant exists k :: 0 <= k < i ==> maxLen == |lists[k]| || i == 0
    {
        if |lists[i]| > maxLen {
            maxLen := |lists[i]|;
        }
        i := i + 1;
    }
    return maxLen;
}