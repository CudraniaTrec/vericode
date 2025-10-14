//Dafny Code

method LargestNegative(a: array<int>) returns (maxNeg: int)
    requires a != null
    ensures (exists i :: 0 <= i < a.Length && a[i] < 0) ==> (maxNeg < 0 && (forall j :: 0 <= j < a.Length && a[j] < 0 ==> a[j] <= maxNeg))
    ensures (forall i :: 0 <= i < a.Length && a[i] >= 0) ==> (maxNeg == 0)
{
    var found := false;
    maxNeg := 0;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant !found ==> maxNeg == 0
        invariant found ==> maxNeg < 0 && (forall j :: 0 <= j < i && a[j] < 0 ==> a[j] <= maxNeg)
    {
        if a[i] < 0 {
            if !found || a[i] > maxNeg {
                maxNeg := a[i];
                found := true;
            }
        }
        i := i + 1;
    }
    if !found {
        maxNeg := 0;
    }
}