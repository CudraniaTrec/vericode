method ContainsNoDuplicates<T>(s: seq<T>) returns (noDups: bool)
    ensures noDups <==> (forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j ==> s[i] != s[j])
{
    noDups := true;
    var n := |s|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant noDups ==> (forall a, b :: 0 <= a < i && 0 <= b < i && a != b ==> s[a] != s[b])
    {
        var j := i + 1;
        while j < n
            invariant i+1 <= n ==> i+1 <= n
            invariant i < n ==> i < n
            invariant i < j <= n
            invariant noDups ==> (forall k :: i+1 <= k < j ==> s[i] != s[k])
        {
            if s[i] == s[j] {
                noDups := false;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}