method FirstElementsOfSublists(sublists: seq<seq<int>>) returns (firsts: seq<int>)
    ensures |firsts| == |sublists|
    ensures forall i :: 0 <= i < |sublists| ==> |sublists[i]| > 0 ==> firsts[i] == sublists[i][0]
    requires forall subs :: subs in sublists ==> |subs| > 0
{
    var res := [];
    var i := 0;
    while i < |sublists|
        invariant 0 <= i <= |sublists|
        invariant |res| == i
        invariant forall j :: 0 <= j < i ==> res[j] == sublists[j][0]
    {
        res := res + [sublists[i][0]];
        i := i + 1;
    }
    firsts := res;
}