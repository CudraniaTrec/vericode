
function MinPair(s: seq<int>) : (r: int)
    requires |s| == 2
    ensures s[0] <= s[1] <==> r == s[0]
    ensures s[0] > s[1] ==> r == s[1] 
{
    if s[0] <= s[1] then s[0] else s[1]
}


function min(s: seq<int>) : (r: int)
    requires |s| >= 2
    ensures forall i :: 0 <= i < |s| ==> r <= s[i]
{
    if |s| == 2 then MinPair(s)
    else MinPair([s[0], min(s[1..])])
}


method SecondSmallest(s: array<int>) returns (secondSmallest: int)
    requires s.Length >= 2
    // There must be at least 2 different values, a minimum and another one
    requires exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] != s[i]
    ensures exists i, j :: 0 <= i < s.Length && 0 <= j < s.Length && i != j && s[i] == min(s[..]) && s[j] == secondSmallest 
    ensures forall k ::  0 <= k < s.Length && s[k] != min(s[..])  ==>  s[k] >= secondSmallest
{
    var minIndex := 0;
    var secondMinIndex := 1;

    if s[1] < s[0] {
        minIndex := 1;
        secondMinIndex := 0;
    }

    // Invariant: 
    //  - minIndex and secondMinIndex are distinct and in 0..i
    //  - s[minIndex] is the minimum of s[0..i)
    //  - s[secondMinIndex] is the minimum of s[0..i) except for s[minIndex]
    //  - for all k in 0..i, if s[k] != s[minIndex], then s[k] >= s[secondMinIndex]
    for i := 2 to s.Length
        invariant 2 <= i <= s.Length
        invariant 0 <= minIndex < i
        invariant 0 <= secondMinIndex < i
        invariant minIndex != secondMinIndex
        invariant forall k :: 0 <= k < i ==> s[minIndex] <= s[k]
        invariant forall k :: 0 <= k < i && k != minIndex ==> s[secondMinIndex] <= s[k]
        invariant forall k :: 0 <= k < i && s[k] != s[minIndex] ==> s[k] >= s[secondMinIndex]
        invariant exists j :: 0 <= j < i && s[j] == s[minIndex]
        invariant exists j :: 0 <= j < i && j != minIndex && s[j] == s[secondMinIndex]
    {
        assert 0 <= minIndex < i;
        assert 0 <= secondMinIndex < i;
        assert minIndex != secondMinIndex;

        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] < s[secondMinIndex] && i != minIndex {
            secondMinIndex := i;
        }
        // assert s[minIndex] <= s[k] for all k in 0..i+1
        // assert s[secondMinIndex] is the minimal value in 0..i+1 except for s[minIndex]
    }

    assert minIndex != secondMinIndex;
    assert forall k :: 0 <= k < s.Length ==> s[minIndex] <= s[k];
    assert forall k :: 0 <= k < s.Length && k != minIndex ==> s[secondMinIndex] <= s[k];
    assert forall k :: 0 <= k < s.Length && s[k] != s[minIndex] ==> s[k] >= s[secondMinIndex];

    secondSmallest := s[secondMinIndex];
}

function abs(a: real) : real {if a>0.0 then a else -a}
