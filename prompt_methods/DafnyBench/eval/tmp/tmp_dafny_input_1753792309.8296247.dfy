
method PairwiseAddition(a: array<int>) returns (result: array<int>)
    requires a != null
    requires a.Length % 2 == 0
    ensures result != null
    ensures result.Length == a.Length / 2
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1]
{
    result := new int[a.Length / 2];
    var i := 0;
    while i < a.Length / 2
        invariant 0 <= i <= a.Length / 2
        invariant result != null
        invariant result.Length == a.Length / 2
        invariant forall j :: 0 <= j < i ==> result[j] == a[2*j] + a[2*j + 1]
    {
        assert 0 <= 2*i < a.Length;
        assert 0 <= 2*i + 1 < a.Length;
        result[i] := a[2*i] + a[2*i + 1];
        i := i + 1;
    }
    assert forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1];
}

function abs(a: real) : real {if a>0.0 then a else -a}
