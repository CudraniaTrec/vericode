method MinListLength(lists: seq<seq<int>>) returns (minLength: int)
    ensures forall s :: s in lists ==> |s| >= minLength
    ensures lists == [] ==> minLength == 0
    ensures lists != [] ==> exists s :: s in lists && |s| == minLength
{
    if |lists| == 0 {
        minLength := 0;
    } else {
        var currentMin := |lists[0]|;
        var i := 1;
        while i < |lists|
            invariant 1 <= |lists| ==> 0 <= i <= |lists|
            invariant 1 <= |lists| ==> currentMin == Min({ |lists[j]| | 0 <= j < i })
        {
            if |lists[i]| < currentMin {
                currentMin := |lists[i]|;
            }
            i := i + 1;
        }
        minLength := currentMin;
    }
}