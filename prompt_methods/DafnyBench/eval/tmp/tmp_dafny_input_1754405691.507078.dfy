
// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
method longestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
{
    i := 0;
    while i < a.Length && i < b.Length && a[i] == b[i]
        invariant 0 <= i <= a.Length && 0 <= i <= b.Length
        invariant a[..i] == b[..i]
        invariant forall j :: 0 <= j < i ==> a[j] == b[j]
    {
        i := i + 1;
    }
    assert i <= a.Length && i <= b.Length;
    assert a[..i] == b[..i];
    assert i < a.Length && i < b.Length ==> a[i] != b[i];
}
 
// Test method with an example.
method testLongestPrefix() {
    var a := new int[] [1, 3, 2, 4, 8];
    var b := new int[] [1, 3, 3, 4];
    var i := longestPrefix(a, b);
}

function abs(a: real) : real {if a>0.0 then a else -a}
