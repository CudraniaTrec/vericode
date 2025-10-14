method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
    ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && (forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i)
    ensures !found ==> (forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j])
{
    c := ' ';
    found := false;
    var inner_found := false;
    var i := 0;
    while i < |s| && !found
        invariant 0 <= i <= |s|
        invariant !found ==> (forall k, l :: 0 <= k < l < i ==> s[k] != s[l])
        invariant !found ==> (forall k :: 0 <= k < i ==> (forall l :: k < l < |s| ==> s[k] != s[l]))
        invariant !found ==> !inner_found
        invariant found ==> inner_found
        invariant found ==> exists ii, jj :: 0 <= ii < jj < |s| && s[ii] == s[jj] && s[ii] == c && (forall k, l :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii)
    {
        var j := i + 1;
        while j < |s| && !inner_found
            invariant i+1 <= j <= |s|
            invariant !inner_found ==> (forall l :: i+1 <= l < j ==> s[i] != s[l])
            invariant !inner_found ==> (forall k, l :: 0 <= k < l < i ==> s[k] != s[l])
            invariant !inner_found ==> (forall k :: 0 <= k < i ==> (forall l :: k < l < |s| ==> s[k] != s[l]))
            invariant inner_found ==> s[i] == s[j-1] && c == s[i]
            invariant inner_found ==> (forall l :: i+1 <= l < j-1 ==> s[i] != s[l])
        {
            if s[i] == s[j] {
                inner_found := true;
                c := s[i];
            }
            j := j + 1;
        }
        found := inner_found;
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
