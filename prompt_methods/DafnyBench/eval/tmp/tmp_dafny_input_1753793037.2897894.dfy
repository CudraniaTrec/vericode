
method IsMinHeap(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
    ensures !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]))
{
    result := true;
    var violated := false;
    var badIndex := -1;
    // Loop to check min-heap property
    // Loop invariant: result ==> forall j :: 0 <= j < i ==> a[j] <= a[2*j + 1] && (2*j + 2 == a.Length || a[j] <= a[2*j + 2])
    // Loop invariant: 0 <= i <= a.Length / 2
    // Loop invariant: !result ==> (exists j :: 0 <= j < i && (a[j] > a[2*j + 1] || (2*j + 2 != a.Length && a[j] > a[2*j + 2])))
    for i := 0 to a.Length / 2
        invariant 0 <= i <= a.Length / 2
        invariant result ==> forall j :: 0 <= j < i ==> a[j] <= a[2*j + 1] && (2*j + 2 == a.Length || a[j] <= a[2*j + 2])
        invariant !result ==> (exists j :: 0 <= j < i && (a[j] > a[2*j + 1] || (2*j + 2 != a.Length && a[j] > a[2*j + 2])))
    {
        assert 0 <= i < a.Length / 2 ==> 2*i + 1 < a.Length;
        if a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]) {
            result := false;
            violated := true;
            badIndex := i;
            break;
        }
    }
    // After the loop
    // If result is true, then for all i in 0..a.Length/2-1, the heap property holds
    assert result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2]);
    // If result is false, then there exists an i where the heap property fails
    assert !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]));
}

function abs(a: real) : real {if a>0.0 then a else -a}
