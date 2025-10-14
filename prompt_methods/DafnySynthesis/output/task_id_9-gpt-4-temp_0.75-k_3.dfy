method MinRotations(s: string) returns (rot: int)
    requires |s| > 0
    ensures 1 <= rot <= |s|
    ensures forall k :: 1 <= k < rot ==> s[..] != s[k..] + s[..k]
    ensures s[..] == s[rot..] + s[..rot]
{
    var n := |s|;
    rot := n;
    // Try all possible rotations from 1 up to n-1
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall k :: 1 <= k < i ==> s != s[k..] + s[..k]
        decreases n - i
    {
        if s == s[i..] + s[..i] {
            rot := i;
            break;
        }
        i := i + 1;
    }
}