method IsLengthOdd(s: string) returns (result: bool)
    ensures result <==> |s| % 2 == 1
{
    // |s| is the length of the string s
    // |s| % 2 == 1 is true iff the length is odd
    assert |s| >= 0;
    result := |s| % 2 == 1;
    assert result <==> |s| % 2 == 1;
}
function abs(a: real) : real {if a>0.0 then a else -a}
