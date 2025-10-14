
method IsMinHeap(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
    ensures !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]))
{
    result := true;
    var broken := false;
    var break_i := 0;
    // Invariant: result ==> forall j :: 0 <= j < i ==> a[j] <= a[2*j + 1] && (2*j + 2 == a.Length || a[j] <= a[2*j + 2])
    // Invariant: !result ==> exists j :: 0 <= j < i && (a[j] > a[2*j + 1] || (2*j + 2 != a.Length && a[j] > a[2*j + 2]))
    // Invariant: 0 <= i <= a.Length / 2
    for i := 0 to a.Length / 2
        invariant 0 <= i <= a.Length / 2
        invariant result ==> forall j :: 0 <= j < i ==> a[j] <= a[2*j + 1] && (2*j + 2 == a.Length || a[j] <= a[2*j + 2])
        invariant !result ==> exists j :: 0 <= j < i && (a[j] > a[2*j + 1] || (2*j + 2 != a.Length && a[j] > a[2*j + 2]))
    {
        if a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]) {
            result := false;
            break_i := i;
            broken := true;
            break;
        }
        assert a[i] <= a[2*i + 1];
        if 2*i + 2 != a.Length {
            assert a[i] <= a[2*i + 2];
        }
    }
    if broken {
        assert exists j :: 0 <= j < break_i + 1 && (a[j] > a[2*j + 1] || (2*j + 2 != a.Length && a[j] > a[2*j + 2]));
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
