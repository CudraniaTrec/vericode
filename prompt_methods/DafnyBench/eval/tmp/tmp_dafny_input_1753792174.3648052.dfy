
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
{
    result := false;
    var found: bool := false;
    var found_i: int := -1;
    var found_j: int := -1;
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant !result ==> forall ii, jj :: 0 <= ii < i && 0 <= jj < b.Length ==> a[ii] != b[jj]
        invariant !result ==> forall ii, jj :: 0 <= ii < i ==> 0 <= jj < b.Length ==> a[ii] != b[jj]
        invariant !result ==> forall ii :: 0 <= ii < i ==> forall jj :: 0 <= jj < b.Length ==> a[ii] != b[jj]
    {
        for j := 0 to b.Length
            invariant 0 <= j <= b.Length
            invariant !result ==> forall jj :: 0 <= jj < j ==> a[i] != b[jj]
        {
            if a[i] == b[j] {
                result := true;
                assert exists ii, jj :: 0 <= ii < a.Length && 0 <= jj < b.Length && a[ii] == b[jj];
                return;
            }
        }
    }
    assert !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j];
}

function abs(a: real) : real {if a>0.0 then a else -a}
