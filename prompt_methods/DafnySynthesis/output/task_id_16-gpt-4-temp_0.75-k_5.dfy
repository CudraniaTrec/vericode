method IsUnderscoreSeparatedLowercase(s: string) returns (res: bool)
{
    // An empty string is not valid
    if s.Length == 0 {
        res := false;
        return;
    }
    var i := 0;
    // Must start with a lowercase letter
    if !(s[0] in 'a'..'z') {
        res := false;
        return;
    }
    while i < s.Length
        invariant 0 <= i <= s.Length
    {
        // Consume a sequence of lowercase letters
        while i < s.Length && s[i] in 'a'..'z'
            invariant 0 <= i <= s.Length
        {
            i := i + 1;
        }
        if i == s.Length {
            res := true;
            return;
        }
        // Next character must be '_'
        if s[i] != '_' {
            res := false;
            return;
        }
        // Underscore cannot be at the end
        if i+1 == s.Length {
            res := false;
            return;
        }
        // Next character after '_' must be a lowercase letter
        if !(s[i+1] in 'a'..'z') {
            res := false;
            return;
        }
        // Move past the underscore
        i := i + 1;
    }
    // If we get here, pattern matched
    res := true;
}