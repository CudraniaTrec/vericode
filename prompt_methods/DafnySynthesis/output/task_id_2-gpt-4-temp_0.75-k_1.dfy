//Dafny Code

method SharedElements(a: array<int>, b: array<int>) returns (result: set<int>)
    ensures result == set x | 0 <= x < a.Length && a[x] in b[..] :: a[x]
{
    var s := {};
    var bSet := set j | 0 <= j < b.Length :: b[j];

    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant s == set x | 0 <= x < i && a[x] in bSet :: a[x]
    {
        if a[i] in bSet {
            s := s + {a[i]};
        }
        i := i + 1;
    }
    result := s;
}