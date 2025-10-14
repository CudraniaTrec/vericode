
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
{
    result := true;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result ==> forall j :: 0 <= j < i ==> n > a[j]
        invariant !result ==> exists j :: 0 <= j < i && n <= a[j]
        invariant result || !result
    {
        if n <= a[i] {
            result := false;
            // At this point, n <= a[i], so the existential holds for j = i
            assert 0 <= i < a.Length && n <= a[i];
            break;
        }
        i := i + 1;
    }
    // After the loop
    if result {
        // We never found n <= a[i], so n > a[j] for all j
        assert forall j :: 0 <= j < a.Length ==> n > a[j];
    } else {
        // We found some i with n <= a[i]
        assert exists j :: 0 <= j < a.Length && n <= a[j];
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
