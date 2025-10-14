method ReverseUptoK(a: array<int>, k: int)
    requires a != null
    requires 0 <= k <= a.Length
    modifies a
    ensures forall i :: 0 <= i < k ==> a[i] == old(a)[k - 1 - i]
    ensures forall i :: k <= i < a.Length ==> a[i] == old(a)[i]
{
    var i := 0;
    var j := k - 1;
    while i < j
        invariant 0 <= i <= j + 1 <= k <= a.Length
        invariant forall m :: 0 <= m < i ==> a[m] == old(a)[k - 1 - m]
        invariant forall n :: j < n < k ==> a[n] == old(a)[k - 1 - n]
        invariant forall p :: k <= p < a.Length ==> a[p] == old(a)[p]
    {
        var tmp := a[i];
        a[i] := a[j];
        a[j] := tmp;
        i := i + 1;
        j := j - 1;
    }
}