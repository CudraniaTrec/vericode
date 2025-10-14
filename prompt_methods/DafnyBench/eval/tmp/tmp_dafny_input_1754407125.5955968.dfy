
method LucidNumbers(n: int) returns (lucid: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
    ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
{
    lucid := [];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall j :: 0 <= j < |lucid| ==> lucid[j] % 3 == 0
        invariant forall j :: 0 <= j < |lucid| ==> lucid[j] <= n
        invariant forall j, k :: 0 <= j < k < |lucid| ==> lucid[j] < lucid[k]
        invariant forall j :: 0 <= j < |lucid| ==> lucid[j] < i
    {
        if i % 3 == 0 {
            lucid := lucid + [i];
            assert lucid[|lucid|-1] == i;
            assert lucid[|lucid|-1] % 3 == 0;
            assert lucid[|lucid|-1] <= n;
            if |lucid| > 1 {
                assert lucid[|lucid|-2] < lucid[|lucid|-1];
            }
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
