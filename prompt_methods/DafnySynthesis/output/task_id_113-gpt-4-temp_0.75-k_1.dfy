method IsStringInteger(s: string) returns (result: bool)
{
    // An empty string cannot represent an integer
    if s.Length == 0 {
        return false;
    }

    var i := 0;
    // Check for optional leading '+' or '-'
    if s[0] == '-' || s[0] == '+' {
        if s.Length == 1 {
            // String is only "+" or "-", not a valid integer
            return false;
        }
        i := 1;
    }

    // All remaining characters must be digits
    while i < s.Length
        invariant 1 <= s.Length ==> 0 <= i <= s.Length
        invariant 0 <= i <= s.Length
        invariant (forall j :: 0 <= j < i ==> '0' <= s[j] <= '9' || (j == 0 && (s[j] == '-' || s[j] == '+')))
    {
        if s[i] < '0' || s[i] > '9' {
            return false;
        }
        i := i + 1;
    }
    return true;
}