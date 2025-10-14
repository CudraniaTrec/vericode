method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
{
    if a.Length == 0 {
        return true;
    }

    var firstElement := a[0];
    result := true;

    var i: int := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant result ==> forall j :: 1 <= j < i ==> a[j] == firstElement
        invariant !result ==> exists j :: 1 <= j < i && a[j] != firstElement
        decreases a.Length - i
    {
        if a[i] != firstElement {
            result := false;
            break;
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
