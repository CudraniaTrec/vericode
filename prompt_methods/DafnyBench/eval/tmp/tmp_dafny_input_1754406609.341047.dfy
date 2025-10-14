method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{
    result := true;
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> forall j :: 0 <= j < i ==> a[j] == n
        invariant !result ==> exists j :: 0 <= j < i && a[j] != n
    {
        if a[i] != n {
            result := false;
            assert a[i] != n;
            break;
        }
        i := i + 1;
    }
    // Post-loop assertion
    assert result ==> forall j :: 0 <= j < a.Length ==> a[j] == n;
    assert !result ==> exists j :: 0 <= j < a.Length && a[j] != n;
}
function abs(a: real) : real {if a>0.0 then a else -a}
