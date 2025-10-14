
method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
{
    v := 0;
    var i: int;
    i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= v
        invariant forall k :: 0 <= k < v ==> k in s[..i]
        invariant forall k :: 0 <= k < i :: s[k] <= s[i-1]  // sorted prefix
        invariant forall k :: 0 <= k < i ==> s[k] >= 0
        invariant forall k :: 0 <= k < i ==> s[k] < v ==> s[k] in s[..i]
        decreases |s| - i
    {
        if s[i] > v
        {
            break;
        }
        else
        {
            if s[i] == v 
            {
                v := v + 1;
            }
        }
        i := i + 1;
    }
    // After the loop:
    assert forall k :: 0 <= k < v ==> k in s[..i];
    assert forall k :: 0 <= k < v ==> k in s;
    assert v !in s[..i];
    assert v !in s;
}

function abs(a: real) : real {if a>0.0 then a else -a}
