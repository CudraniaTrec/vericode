method MoveZeroesToEnd(a: array<int>)
    requires a != null
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures forall i :: 0 <= i < a.Length - (|old(a[..])| - |old(a[..]).Filter(x => x == 0)|) ==> a[i] != 0
    ensures forall i :: a.Length - (|old(a[..])| - |old(a[..]).Filter(x => x == 0)|) <= i < a.Length ==> a[i] == 0
{
    var n := a.Length;
    var insert := 0;
    // Move all non-zero elements to the front
    for i := 0 to n - 1
        invariant 0 <= insert <= i + 1 <= n
        invariant forall k :: 0 <= k < insert ==> a[k] != 0
        invariant forall k :: insert <= k <= i ==> a[k] == 0
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if a[i] != 0 {
            a[insert], a[i] := a[i], a[insert];
            insert := insert + 1;
        }
    }
    // Now all non-zero elements are at the front, and zeroes at the end
}