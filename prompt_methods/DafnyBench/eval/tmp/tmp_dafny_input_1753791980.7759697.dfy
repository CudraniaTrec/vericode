
method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
{
    maxList := lists[0];

    var j := 0;
    // Loop to find the index of the longest list
    for i := 1 to |lists|
        invariant 1 <= i <= |lists|
        invariant maxList in lists[..i]
        invariant forall k :: 0 <= k < i ==> |lists[k]| <= |maxList|
        invariant maxList == lists[j]
        invariant 0 <= j < i
    {
        if |lists[i]| > |maxList| {
            maxList := lists[i];
            j := i;
        }
    }
    assert maxList in lists;
    assert forall l :: l in lists ==> |l| <= |maxList|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
