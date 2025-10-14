
method FindMedian(a: array<int>, b: array<int>) returns (median: int)
    requires a != null && b != null
    requires a.Length == b.Length
    requires a.Length > 0
    requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
    requires forall i :: 0 <= i < b.Length - 1 ==> b[i] <= b[i + 1]
    ensures median == if (a.Length % 2 == 0) then (a[a.Length / 2 - 1] + b[0]) / 2 else a[a.Length / 2]
{
    // a and b are non-null, same length, sorted, and non-empty
    assert a != null && b != null;
    assert a.Length == b.Length;
    assert a.Length > 0;
    assert forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1];
    assert forall i :: 0 <= i < b.Length - 1 ==> b[i] <= b[i + 1];

    if (a.Length % 2 == 0) {
        // a.Length is even, so a.Length / 2 - 1 >= 0
        assert a.Length / 2 - 1 >= 0;
        assert a.Length / 2 - 1 < a.Length;
        assert 0 < b.Length;
        assert 0 < a.Length;
        median := (a[a.Length / 2 - 1] + b[0]) / 2;
        assert median == (a[a.Length / 2 - 1] + b[0]) / 2;
    } else {
        // a.Length is odd, so a.Length / 2 is a valid index
        assert 0 <= a.Length / 2 < a.Length;
        median := a[a.Length / 2];
        assert median == a[a.Length / 2];
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
