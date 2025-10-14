method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
{
    result := [];
    var i: int := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == lst[j][0]
    {
        result := result + [lst[i][0]];
        i := i + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
