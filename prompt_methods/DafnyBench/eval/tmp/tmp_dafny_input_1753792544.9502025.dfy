
method Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>) returns (r: seq<int>)
    requires |s1| == |s2| && |s2| == |s3|
    ensures |r| == 3 * |s1|
    ensures forall i :: 0 <= i < |s1| ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i]
{
    r := [];
    var n := |s1|;
    // Loop invariant annotations
    // At each iteration i, r contains the first i interleaved triples
    for i := 0 to n
        invariant 0 <= i <= n
        invariant |r| == 3 * i
        invariant forall j :: 0 <= j < i ==> r[3*j] == s1[j] && r[3*j + 1] == s2[j] && r[3*j + 2] == s3[j]
    {
        r := r + [s1[i], s2[i], s3[i]];
        assert |r| == 3 * (i + 1);
        assert forall j :: 0 <= j < i + 1 ==> r[3*j] == s1[j] && r[3*j + 1] == s2[j] && r[3*j + 2] == s3[j];
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
