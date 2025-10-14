//Dafny Code

method ElementWiseDivision(xs: seq<real>, ys: seq<real>) returns (result: seq<real>)
    requires |xs| == |ys|
    requires forall y :: y in ys ==> y != 0.0
    ensures |result| == |xs|
    ensures forall i :: 0 <= i < |xs| ==> result[i] == xs[i] / ys[i]
{
    var res := [];
    var n := |xs|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |res| == i
        invariant forall j :: 0 <= j < i ==> res[j] == xs[j] / ys[j]
    {
        res := res + [xs[i] / ys[i]];
        i := i + 1;
    }
    result := res;
}