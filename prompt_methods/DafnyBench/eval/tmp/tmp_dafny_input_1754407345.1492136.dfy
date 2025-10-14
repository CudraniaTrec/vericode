
method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
    ensures result ==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
    ensures !result ==> !(exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2)
{
    result := false;
    var found := false;
    var idx := -1;
    // Loop to find if such a '.' exists
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant !result ==> (forall j :: 0 <= j < i ==> !(s[j] == '.' && |s| - j - 1 == 2))
        invariant result ==> (exists j :: 0 <= j < i && s[j] == '.' && |s| - j - 1 == 2)
    {
        if s[i] == '.' && |s| - i - 1 == 2 {
            result := true;
            // assert (exists j :: 0 <= j < |s| && s[j] == '.' && |s| - j - 1 == 2);
            break;
        }
        i := i + 1;
    }
    // assert result <==> (exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2);
}

function abs(a: real) : real {if a>0.0 then a else -a}
