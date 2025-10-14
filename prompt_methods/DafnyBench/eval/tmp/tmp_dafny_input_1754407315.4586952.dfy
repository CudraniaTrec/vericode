method AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
    ensures |r| == |l| + 1
    ensures r[|r| - 1] == t
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
    // r will be l concatenated with [t]
    r := l + [t];
    assert |r| == |l| + 1;
    assert r[|r| - 1] == t;
    assert forall i :: 0 <= i < |l| ==> r[i] == l[i];
}
function abs(a: real) : real {if a>0.0 then a else -a}
