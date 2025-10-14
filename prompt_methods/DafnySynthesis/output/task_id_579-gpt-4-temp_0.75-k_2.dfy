// Dafny Code

method DissimilarElements(a: array<int>, b: array<int>) returns (result: set<int>)
    ensures result == (set i | 0 <= i < a.Length :: a[i]) + (set j | 0 <= j < b.Length :: b[j]) 
                     - ((set i | 0 <= i < a.Length :: a[i]) * (set j | 0 <= j < b.Length :: b[j]))
{
    var setA := set i | 0 <= i < a.Length :: a[i];
    var setB := set j | 0 <= j < b.Length :: b[j];
    result := (setA + setB) - (setA * setB);
}