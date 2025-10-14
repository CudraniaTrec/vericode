method EveryOddIndexHasOddNumber(a: array<int>) returns (res: bool)
{
    res := true;
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 1 <= j < i ==> a[j] % 2 != 0
        decreases a.Length - i
    {
        if a[i] % 2 == 0 {
            res := false;
            return;
        }
        i := i + 2;
    }
}