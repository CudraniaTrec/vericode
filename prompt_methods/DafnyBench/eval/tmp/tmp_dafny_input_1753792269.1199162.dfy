
method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
{
    minSublist := s[0];
    var n := |s|;
    // Loop invariant: 1 <= i <= n
    // minSublist is always one of the first i sublists
    // For all j < i, |minSublist| <= |s[j]|
    for i := 1 to n
        invariant 1 <= i <= n
        invariant minSublist in s[..i]
        invariant forall j :: 0 <= j < i ==> |minSublist| <= |s[j]|
    {
        if |s[i]| < |minSublist| {
            minSublist := s[i];
        }
        // assert minSublist in s[..i+1];
        // assert forall j :: 0 <= j < i+1 ==> |minSublist| <= |s[j]|;
    }
    // assert minSublist in s;
    // assert forall sublist :: sublist in s ==> |minSublist| <= |sublist|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
