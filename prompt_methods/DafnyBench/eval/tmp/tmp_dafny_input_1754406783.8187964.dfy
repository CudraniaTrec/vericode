
method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
    requires |s| > 0
    ensures minSublist in s
    ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
{
    minSublist := s[0];
    var i: int := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant minSublist in s[..i]
        invariant forall j :: 0 <= j < i ==> |minSublist| <= |s[j]|
    {
        if |s[i]| < |minSublist| {
            minSublist := s[i];
        }
        i := i + 1;
    }
    assert minSublist in s;
    assert forall sublist :: sublist in s ==> |minSublist| <= |sublist|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
