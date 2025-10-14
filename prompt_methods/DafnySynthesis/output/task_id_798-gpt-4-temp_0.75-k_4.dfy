//Dafny Code

method SumArray(a: array<int>) returns (sum: int)
    requires a != null
    ensures sum == (if a.Length == 0 then 0 else (sum i | 0 <= i < a.Length :: a[i]))
{
    var s := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant s == (sum j | 0 <= j < i :: a[j])
    {
        s := s + a[i];
        i := i + 1;
    }
    sum := s;
}