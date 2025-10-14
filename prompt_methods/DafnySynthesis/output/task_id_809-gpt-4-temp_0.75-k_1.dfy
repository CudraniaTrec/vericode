method AllSecondSmaller(s1: seq<int>, s2: seq<int>) returns (res: bool)
    ensures res <==> |s1| == |s2| && forall i :: 0 <= i < |s1| ==> s2[i] < s1[i]
{
    if |s1| != |s2| {
        return false;
    }
    var i := 0;
    while i < |s1|
        invariant 0 <= i <= |s1|
        invariant forall j :: 0 <= j < i ==> s2[j] < s1[j]
    {
        if !(s2[i] < s1[i]) {
            return false;
        }
        i := i + 1;
    }
    return true;
}