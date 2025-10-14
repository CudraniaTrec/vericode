
method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
{
    v := |s[0]|;
    var j := 1;
    while j < |s|
        invariant 1 <= |s|
        invariant 1 <= j <= |s|
        invariant forall k :: 0 <= k < j ==> v <= |s[k]|
        invariant exists k :: 0 <= k < j && v == |s[k]|
    {
        if |s[j]| < v
        {
            v := |s[j]|;
        }
        j := j + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
