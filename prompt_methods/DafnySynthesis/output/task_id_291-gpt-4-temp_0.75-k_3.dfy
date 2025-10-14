//Dafny Code

method NumWays(n: int, k: int) returns (ways: int)
    requires n >= 0 && k >= 0
    ensures ways >= 0
{
    if n == 0 || k == 0 {
        ways := 0;
        return;
    }
    if n == 1 {
        ways := k;
        return;
    }

    var same := 0;
    var diff := k;
    // For n == 2:
    // same: both posts same color: k choices
    // diff: both posts different color: k*(k-1) choices
    for i := 2 to n {
        var prev_diff := diff;
        var prev_same := same;

        same := prev_diff; // Last two posts same color: previous two posts must have been different
        diff := (prev_diff + prev_same) * (k - 1); // Last post different: choose any color except last one

        // Prevent integer overflow (optional, since Dafny ints are unbounded)
        // if diff < 0 || same < 0 {
        //     ways := 0;
        //     return;
        // }
    }
    ways := same + diff;
}