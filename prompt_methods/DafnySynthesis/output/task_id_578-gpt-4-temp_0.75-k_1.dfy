method Interleave3Seqs<T>(a: seq<T>, b: seq<T>, c: seq<T>) returns (res: seq<T>)
    requires |a| == |b| && |b| == |c|
    ensures |res| == 3 * |a|
    ensures forall i :: 0 <= i < |a| ==> res[3 * i] == a[i] && res[3 * i + 1] == b[i] && res[3 * i + 2] == c[i]
{
    var n := |a|;
    var r := [];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |r| == 3 * i
        invariant forall j :: 0 <= j < i ==> r[3*j] == a[j] && r[3*j+1] == b[j] && r[3*j+2] == c[j]
    {
        r := r + [a[i], b[i], c[i]];
        i := i + 1;
    }
    res := r;
}