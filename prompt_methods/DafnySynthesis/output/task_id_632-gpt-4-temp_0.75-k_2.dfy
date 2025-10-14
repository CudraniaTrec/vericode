method MoveZeroesToEnd(a: array<int>)
    requires a != null
    modifies a
    ensures multiset a[..] == old(multiset a[..])
    ensures (forall i :: 0 <= i < (|a| - NumOfZeros(a[..])) ==> a[i] != 0)
    ensures (forall i :: (|a| - NumOfZeros(a[..])) <= i < |a| ==> a[i] == 0)
{
    var n := a.Length;
    var pos := 0;
    // Move non-zero elements forward
    for i := 0 to n-1
        invariant 0 <= pos <= i + 1 <= n
        invariant multiset a[..] == old(multiset a[..])
        invariant (forall j :: 0 <= j < pos ==> a[j] != 0)
        invariant (forall j :: pos <= j <= i ==> a[j] == 0)
    {
        if a[i] != 0 {
            a[pos], a[i] := a[i], a[pos];
            pos := pos + 1;
        }
    }
    // All elements after pos are zeros
}

function NumOfZeros(s: seq<int>): int
{
    if |s| == 0 then 0 else (if s[0] == 0 then 1 else 0) + NumOfZeros(s[1..])
}