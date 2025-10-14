
method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
{
    v := |s[0]|;
    var i: int := 1;
    while i <= |s|
        invariant 1 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> v <= |s[j]|
        invariant exists j :: 0 <= j < i && v == |s[j]|
    {
        if |s[i]| < v
        {
            v := |s[i]|;
        }
        i := i + 1;
    }
    assert forall j :: 0 <= j < |s| ==> v <= |s[j]|;
    assert exists j :: 0 <= j < |s| && v == |s[j]|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
