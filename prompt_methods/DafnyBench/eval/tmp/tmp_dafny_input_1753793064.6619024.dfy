
method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
    result := false;
    var found := false;
    var j := 0;
    while j < |s|
        invariant 0 <= j <= |s|
        invariant !result ==> (forall k :: 0 <= k < j ==> !(s[k] == '.' && |s| - k - 1 == 2))
        invariant result ==> (exists k :: 0 <= k < j && s[k] == '.' && |s| - k - 1 == 2)
    {
        if s[j] == '.' && |s| - j - 1 == 2 {
            result := true;
            break;
        }
        j := j + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
