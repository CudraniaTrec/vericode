method MinLengthSublist(arr: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |arr| > 0
    ensures minSublist in arr
    ensures forall s :: s in arr ==> |minSublist| <= |s|
{
    var minIdx := 0;
    var minLen := |arr[0]|;
    var i := 1;
    while i < |arr|
        invariant 0 <= minIdx < |arr|
        invariant minLen == |arr[minIdx]|
        invariant forall j :: 0 <= j < i ==> |arr[minIdx]| <= |arr[j]|
        decreases |arr| - i
    {
        if |arr[i]| < minLen {
            minLen := |arr[i]|;
            minIdx := i;
        }
        i := i + 1;
    }
    minSublist := arr[minIdx];
}