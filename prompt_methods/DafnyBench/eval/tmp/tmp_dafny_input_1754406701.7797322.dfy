
method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
{
    var rearChars: seq<char> := [];
    var i: int := 0;
    while i < |l|
        invariant 0 <= i <= |l|
        invariant |rearChars| == i
        invariant forall j :: 0 <= j < i ==> rearChars[j] == l[j][|l[j]| - 1]
    {
        assert 0 <= i < |l|;
        assert |l[i]| > 0;
        rearChars := rearChars + [l[i][|l[i]| - 1]];
        i := i + 1;
    }
    r := rearChars;
}

function abs(a: real) : real {if a>0.0 then a else -a}
