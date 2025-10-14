method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    ensures maxList in lists || lists == []
    ensures forall s: seq<int> :: s in lists ==> |maxList| >= |s|
    ensures lists == [] ==> maxList == []
{
    if |lists| == 0 {
        maxList := [];
    } else {
        var maxSoFar := lists[0];
        var i := 1;
        while i < |lists|
            invariant 1 <= |lists| ==> 0 <= i <= |lists|
            invariant maxSoFar in lists[..i]
            invariant forall k :: 0 <= k < i ==> |maxSoFar| >= |lists[k]|
        {
            if |lists[i]| > |maxSoFar| {
                maxSoFar := lists[i];
            }
            i := i + 1;
        }
        maxList := maxSoFar;
    }
}