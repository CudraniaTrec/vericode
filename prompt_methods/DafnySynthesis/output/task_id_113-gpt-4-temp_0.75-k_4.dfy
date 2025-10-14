method IsIntegerString(s: string) returns (res: bool)
{
    if s == "" {
        // Empty string is not a valid integer
        res := false;
        return;
    }

    var i := 0;
    var n := s.Length;

    // Optional '+' or '-' at the beginning
    if s[0] == '+' as int || s[0] == '-' as int {
        i := 1;
        if n == 1 {
            // Only sign, no digits
            res := false;
            return;
        }
    }

    // At least one digit is required
    while i < n
        invariant 0 <= i <= n
    {
        var c := s[i];
        if c < '0' as int || c > '9' as int {
            res := false;
            return;
        }
        i := i + 1;
    }

    res := true;
}