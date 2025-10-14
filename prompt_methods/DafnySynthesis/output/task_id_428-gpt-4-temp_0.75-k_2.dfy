// Dafny Code
method ShellSort(a: array<int>)
    requires a != null
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures forall i: int, j: int :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
    var n := a.Length;
    var gap := n / 2;
    while gap > 0
        invariant 0 <= gap <= n/2
        invariant a != null
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var i := gap;
        while i < n
            invariant gap <= i <= n
            invariant multiset(a[..]) == multiset(old(a[..]))
        {
            var temp := a[i];
            var j := i;
            while j >= gap && a[j - gap] > temp
                invariant gap <= j <= n
                invariant multiset(a[..]) == multiset(old(a[..]))
                decreases j
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