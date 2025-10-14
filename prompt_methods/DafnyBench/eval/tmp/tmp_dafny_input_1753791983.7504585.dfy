method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
{
    maxList := lists[0];

    var i := 1;
    while i < |lists|
        invariant 1 <= i <= |lists|
        invariant maxList in lists[..i]
        invariant forall k :: 0 <= k < i ==> |lists[k]| <= |maxList|
    {
        if |lists[i]| > |maxList| {
            maxList := lists[i];
        }
        i := i + 1;
    }
    assert maxList in lists;
    assert forall l :: l in lists ==> |l| <= |maxList|;
}
function abs(a: real) : real {if a>0.0 then a else -a}
