method fillK(a: array<int>, n: int, k: int, c: int) returns (b: bool)
    requires 0 <= c <= n
    requires n == a.Length
{
    if c == 0 {
        return true;
    }

    var p := 0;
    while p < c
        invariant 0 <= p <= c
        invariant forall i :: 0 <= i < p ==> a[i] == k
    {
        if a[p] != k
        {
            return false;
        }

        p := p + 1;
    }
    assert forall i :: 0 <= i < c ==> a[i] == k;
    return true;
}


method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
    requires 0 <= b.Length <= a.Length
{
    pos := -1;

    if b.Length == 0 {
        return pos;
    }

    var p := 0;

    while p <= a.Length - b.Length
        invariant 0 <= p <= a.Length - b.Length + 1
        invariant pos == -1
        invariant forall j {:trigger a[j]} :: 0 <= j < p ==> (exists i :: 0 <= i < b.Length && a[j + i] != b[i])
    {
        var i := 0;
        while i < b.Length
            invariant 0 <= i <= b.Length
            invariant forall j :: 0 <= j < i ==> a[p + j] == b[j]
        {
            if a[p + i] != b[i] {
                break;
            }
            i := i + 1;
        }
        if i == b.Length {
            pos := p;
            return pos;
        }
        p := p + 1;
    }

    return pos;
}
function abs(a: real) : real {if a>0.0 then a else -a}
