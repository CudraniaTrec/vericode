
method ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
    requires |first| > 0
    ensures |result| == |first| - 1 + |second|
    ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
    ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
{
    // first[0..|first|-1] is the sequence of all but the last element of first
    assert |first[0..|first|-1]| == |first| - 1;
    result := first[0..|first| - 1] + second;
    assert |result| == |first[0..|first|-1]| + |second|;
    assert |result| == |first| - 1 + |second|;
    assert forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i];
    assert forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1];
}

function abs(a: real) : real {if a>0.0 then a else -a}
