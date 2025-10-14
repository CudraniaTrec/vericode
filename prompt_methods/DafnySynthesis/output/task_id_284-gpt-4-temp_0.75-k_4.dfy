method AllElementsEqual<T>(a: array<T>, elem: T) returns (allEqual: bool)
    requires a != null
{
    var i := 0;
    allEqual := true;
    while i < a.Length && allEqual
        invariant 0 <= i <= a.Length
        invariant allEqual ==> forall j :: 0 <= j < i ==> a[j] == elem
    {
        if a[i] != elem {
            allEqual := false;
        }
        i := i + 1;
    }
}