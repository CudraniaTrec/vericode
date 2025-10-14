
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

    // Invariant: 0 <= minIndex < i && 0 <= secondMinIndex < i && minIndex != secondMinIndex
    // Invariant: forall k :: 0 <= k < i ==> s[minIndex] <= s[k]
    // Invariant: forall k :: 0 <= k < i && k != minIndex ==> s[secondMinIndex] <= s[k] || s[k] == s[minIndex]
    // Invariant: s[secondMinIndex] >= s[minIndex]
    for i := 2 to s.Length
        invariant 2 <= i <= s.Length
        invariant 0 <= minIndex < i
        invariant 0 <= secondMinIndex < i
        invariant minIndex != secondMinIndex
        invariant forall k :: 0 <= k < i ==> s[minIndex] <= s[k]
        invariant forall k :: 0 <= k < i && k != minIndex ==> s[secondMinIndex] <= s[k] || s[k] == s[minIndex]
        invariant s[secondMinIndex] >= s[minIndex]
    {
        if s[i] < s[minIndex] {
            secondMinIndex := minIndex;
            minIndex := i;
        } else if s[i] < s[secondMinIndex] && i != minIndex {
            secondMinIndex := i;
        } else if minIndex == secondMinIndex && s[i] != s[minIndex] {
            // Handle the case where all previous values were equal
            secondMinIndex := i;
        }
        assert minIndex != secondMinIndex;
        assert 0 <= minIndex < i+1;
        assert 0 <= secondMinIndex < i+1;
    }

    assert minIndex != secondMinIndex;
    assert 0 <= minIndex < s.Length;
    assert 0 <= secondMinIndex < s.Length;
    assert forall k :: 0 <= k < s.Length ==> s[minIndex] <= s[k];
    assert forall k :: 0 <= k < s.Length && k != minIndex ==> s[secondMinIndex] <= s[k] || s[k] == s[minIndex];
    assert s[secondMinIndex] >= s[minIndex];

    secondSmallest := s[secondMinIndex];
}

function abs(a: real) : real {if a>0.0 then a else -a}
