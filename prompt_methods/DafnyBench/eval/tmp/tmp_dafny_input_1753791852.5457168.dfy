method CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    // |s| >= 0, so the formula always produces a non-negative integer
    assert |s| >= 0;
    assert (|s| * (|s| + 1)) % 2 == 0; // always even, since one of |s| or |s|+1 is even
    count := (|s| * (|s| + 1)) / 2;
    assert count >= 0;
    assert count == (|s| * (|s| + 1)) / 2;
}
function abs(a: real) : real {if a>0.0 then a else -a}
