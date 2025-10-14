// Dafny Code

method NumWaysToPaintFence(n: nat, k: nat) returns (ways: nat)
    requires k >= 1
{
    if n == 0 {
        ways := 0;
        return;
    }
    if n == 1 {
        ways := k;
        return;
    }

    var same: nat := 0;
    var diff: nat := k;
    // same: ways where last two posts are same color
    // diff: ways where last two posts are different colors

    var i: nat := 2;
    while i <= n
        invariant 2 <= i <= n+1
        invariant same <= k * (k-1) ** (i-2)
        invariant diff <= k * (k-1) ** (i-1)
    {
        var prev_diff := diff;
        diff := (same + diff) * (k-1);
        same := prev_diff;
        i := i + 1;
    }
    ways := same + diff;
}