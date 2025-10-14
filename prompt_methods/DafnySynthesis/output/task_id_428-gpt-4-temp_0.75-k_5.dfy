//Dafny Code

method ShellSort(a: array<int>)
    modifies a
    ensures a != null && a.Length == old(a.Length)
    ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
    if a == null || a.Length <= 1 {
        return;
    }
    var n := a.Length;
    var gap := n / 2;
    while gap > 0
        invariant 0 <= gap <= n / 2
        invariant a != null && a.Length == n
    {
        var i := gap;
        while i < n
            invariant gap <= i <= n
            invariant a != null && a.Length == n
        {
            var temp := a[i];
            var j := i;
            while j >= gap && a[j - gap] > temp
                invariant gap <= j <= i
                invariant a != null && a.Length == n
            {
                a[j] := a[j - gap];
                j := j - gap;
            }
            a[j] := temp;
            i := i + 1;
        }
        gap := gap / 2;
    }
}