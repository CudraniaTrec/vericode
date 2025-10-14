
// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/0HRr

// Author of solution:    Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/8pxWd

// Use the command
//   dafny LinearSearch-skeleton.dfy
// or
//   compile LinearSearch-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.



method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
{
    if j == i
    {
        k := -1;
        return;
    }
    if a[j-1] == x
    {
        k := j-1;
        return;

    }
    else
    {
        k := SearchRecursive(a, i, j-1, x);
        assert i <= k < j-1 || k == -1;
        assert k != -1 ==> a[k] == x;
        assert k != -1 ==> forall r | k < r < j-1 :: a[r] != x;
        assert k == -1 ==> forall r | i <= r < j-1 :: a[r] != x;
        // Show that postconditions hold for j
        // If k != -1, then k < j-1 < j, so i <= k < j
        // If k == -1, then need to show forall r | i <= r < j :: a[r] != x
        // But a[j-1] != x, and for r < j-1, a[r] != x by recursive call
        assert k != -1 ==> forall r | k < r < j :: a[r] != x;
        assert k == -1 ==> forall r | i <= r < j :: a[r] != x;
    }
}





method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
{
    if i == j
    {
        return -1;
    }

    var t := j;
    while t > i
        invariant i <= t <= j;
        invariant forall r | t <= r < j :: a[r] != x;
        decreases t
    {
        if a[t-1] == x
        {
            k := t-1;
            assert i <= k < j;
            assert a[k] == x;
            assert forall r | k < r < j :: a[r] != x;
            return;
        }
        else 
        {
            t := t - 1;
        }
    }
    // At this point, t == i, and forall r | i <= r < j :: a[r] != x
    k := -1;
    assert forall r | i <= r < j :: a[r] != x;
}

function abs(a: real) : real {if a>0.0 then a else -a}
