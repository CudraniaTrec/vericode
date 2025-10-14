method MinRotations(s: string) returns (rot: int)
    requires |s| > 0
    ensures 1 <= rot <= |s|
    ensures forall k :: 1 <= k < rot ==> s != s[k..] + s[..k]
    ensures s == s[rot..] + s[..rot]
{
    var n := |s|;
    // Try all possible rotation counts from 1 to n
    rot := n;
    // For k = 1 to n-1
    for k := 1 to n - 1
        invariant 1 <= k <= n
        invariant 1 <= rot <= n
        invariant forall m :: 1 <= m < k ==> s != s[m..] + s[..m]
    {
        if s == s[k..] + s[..k] {
            rot := k;
            return;
        }
    }
}