method SmallestMissingNumber(a: seq<nat>) returns (missing: nat)
    requires forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i+1]
    ensures (forall i :: 0 <= i < |a| ==> a[i] != missing) && 
            (forall n :: 0 <= n < missing ==> exists j :: 0 <= j < |a| && a[j] == n)
{
    var left := 0;
    var right := |a|;

    while left < right
        invariant 0 <= left <= right <= |a|
        invariant forall i :: 0 <= i < left ==> a[i] == i
        invariant (right < |a| ==> a[right] != right)
    {
        var mid := left + (right - left) / 2;
        if mid < |a| && a[mid] == mid {
            left := mid + 1;
        } else {
            right := mid;
        }
    }
    missing := left;
}