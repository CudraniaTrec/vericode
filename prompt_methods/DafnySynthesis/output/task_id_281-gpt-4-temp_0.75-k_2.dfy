// Dafny Code

method AreElementsUnique(a: array<int>) returns (unique: bool)
    ensures unique == (|set i | 0 <= i < a.Length :: a[i]| == a.Length)
{
    var seen := set int{};
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant seen == set j | 0 <= j < i :: a[j]
    {
        if a[i] in seen {
            unique := false;
            return;
        }
        seen := seen + {a[i]};
        i := i + 1;
    }
    unique := true;
}