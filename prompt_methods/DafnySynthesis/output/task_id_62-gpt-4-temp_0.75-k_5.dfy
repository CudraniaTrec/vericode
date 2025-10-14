//Dafny Code

method FindMin(a: array<int>) returns (min: int)
    requires a != null && a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> min <= a[i]
    ensures exists i :: 0 <= i < a.Length && min == a[i]
{
    var m := a[0];
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> m <= a[j]
        invariant exists j :: 0 <= j < i && m == a[j]
    {
        if a[i] < m {
            m := a[i];
        }
        i := i + 1;
    }
    min := m;
}