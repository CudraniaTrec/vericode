// Dafny Code

method ContainsK(s: seq<int>, k: int) returns (found: bool)
{
    found := false;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant found == (exists j :: 0 <= j < i && s[j] == k)
    {
        if s[i] == k {
            found := true;
            break;
        }
        i := i + 1;
    }
}