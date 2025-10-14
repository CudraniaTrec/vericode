method CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    // |s| >= 0 by definition of string length
    // (|s| * (|s| + 1)) is always even, so division by 2 is safe
    count := (|s| * (|s| + 1)) / 2;
    // count >= 0 because |s| >= 0
    // count == (|s| * (|s| + 1)) / 2 by assignment
}
function abs(a: real) : real {if a>0.0 then a else -a}
