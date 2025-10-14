method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<real>)
    requires |a| == |b|
    requires forall x :: x in b ==> x != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] as real / b[i] as real
{
    var temp := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |temp| == i
        invariant forall j :: 0 <= j < i ==> temp[j] == a[j] as real / b[j] as real
    {
        temp := temp + [a[i] as real / b[i] as real];
        i := i + 1;
    }
    result := temp;
}