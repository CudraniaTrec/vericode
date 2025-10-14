// Dafny Code

method ReverseUptoK(a: array<int>, k: int)
    requires a != null
    requires 0 <= k <= a.Length
    modifies a
    ensures forall i :: 0 <= i < k ==> a[i] == old(a)[k - 1 - i]
    ensures forall i :: k <= i < a.Length ==> a[i] == old(a)[i]
{
    var left := 0;
    var right := k - 1;
    while left < right
        invariant 0 <= left <= right + 1 <= k <= a.Length
        invariant forall i :: 0 <= i < left ==> a[i] == old(a)[k - 1 - i]
        invariant forall i :: right < i < k ==> a[i] == old(a)[k - 1 - i]
        invariant forall i :: k <= i < a.Length ==> a[i] == old(a)[i]
    {
        var temp := a[left];
        a[left] := a[right];
        a[right] := temp;
        left := left + 1;
        right := right - 1;
    }
}