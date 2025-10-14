
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
        invariant forall k :: 0 <= k < |lucid| ==> lucid[k] % 3 == 0
        invariant forall k :: 0 <= k < |lucid| ==> lucid[k] <= n
        invariant forall k, l :: 0 <= k < l < |lucid| ==> lucid[k] < lucid[l]
        invariant |lucid| == ((i + 2) / 3)
        invariant forall m :: 0 <= m < i ==> (m % 3 == 0 ==> lucid[(m / 3)] == m)
        decreases n - i + 1
    {
        if i % 3 == 0 {
            assert i % 3 == 0;
            assert i <= n;
            lucid := lucid + [i];
            assert |lucid| == ((i / 3) + 1);
        }
        i := i + 1;
    }
    assert forall k :: 0 <= k < |lucid| ==> lucid[k] % 3 == 0;
    assert forall k :: 0 <= k < |lucid| ==> lucid[k] <= n;
    assert forall k, l :: 0 <= k < l < |lucid| ==> lucid[k] < lucid[l];
}

function abs(a: real) : real {if a>0.0 then a else -a}
