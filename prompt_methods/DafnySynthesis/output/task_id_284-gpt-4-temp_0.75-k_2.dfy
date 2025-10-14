method AllElementsEqualTo<T>(a: array<T>, x: T) returns (result: bool)
    requires a != null
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] == x
    {
        if a[i] != x {
            return false;
        }
        i := i + 1;
    }
    return true;
}