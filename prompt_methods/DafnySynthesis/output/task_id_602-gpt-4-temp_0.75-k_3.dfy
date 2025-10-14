method FirstRepeatedChar(s: string) returns (c: char, found: bool)
{
    var seen := set char{};
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant seen == set j | 0 <= j < i :: s[j]
    {
        if s[i] in seen {
            c := s[i];
            found := true;
            return;
        }
        seen := seen + {s[i]};
        i := i + 1;
    }
    found := false;
}