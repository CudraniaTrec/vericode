method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
{
    v := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= v <= if |s| == 0 then 1 else s[|s|-1] + 2
        invariant forall k :: 0 <= k < v ==> k in s[..i]
        invariant forall j :: 0 <= j < i ==> s[j] < v
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
    // At this point, either i == |s| or s[i] > v
    // All numbers < v are in s[..i], and s is sorted, so also in s
    // v is not in s[..i], and since s is sorted and s[i] > v (if i < |s|), v is not in s[i..]
    // So v is not in s
}
function abs(a: real) : real {if a>0.0 then a else -a}
