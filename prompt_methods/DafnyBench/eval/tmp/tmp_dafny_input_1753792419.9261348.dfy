
method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{
    v := [];
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |v| == i
        invariant forall j :: 0 <= j < i ==> v[j] == s[j]
    {
        v := v + [s[i]];
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
