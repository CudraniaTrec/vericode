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
        decreases a.Length - i
    {
        if a[i] != n {
            result := false;
            // At this point, a[i] != n, so !result and such an index exists
            assert 0 <= i < a.Length && a[i] != n;
            break;
        }
        i := i + 1;
    }
    // After the loop: either result is false (so exists j < i with a[j] != n), or i == a.Length
    // If result is true, then all a[0..a.Length-1] == n
    assert result ==> forall j :: 0 <= j < a.Length ==> a[j] == n;
    assert !result ==> exists j :: 0 <= j < a.Length && a[j] != n;
}
function abs(a: real) : real {if a>0.0 then a else -a}
