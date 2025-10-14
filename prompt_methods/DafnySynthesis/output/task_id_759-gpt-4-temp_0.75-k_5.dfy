method IsDecimalWithTwoPrecision(s: string) returns (result: bool)
{
    // The pattern is: optional digits, then optional '.', then exactly two digits
    // Valid examples: "12.34", "0.12", ".12", "123456.00"
    // Invalid examples: "12.3", "12.", "12.345", "abc", "12"

    if |s| < 4 {
        // Minimum: ".12" (length 3), but also "0.12" (length 4)
        if |s| == 3 && s[0] == '.' && ('0' <= s[1] <= '9') && ('0' <= s[2] <= '9') {
            return true;
        } else {
            return false;
        }
    }
    var i := 0;
    // Optional leading digits
    while i < |s| && '0' <= s[i] <= '9'
        decreases |s| - i
    {
        i := i + 1;
    }
    // Now expect a '.'
    if i >= |s| || s[i] != '.' {
        return false;
    }
    i := i + 1;
    // Need exactly two digits after the dot
    if i + 1 >= |s| {
        return false;
    }
    if !('0' <= s[i] <= '9') || !('0' <= s[i+1] <= '9') {
        return false;
    }
    i := i + 2;
    // No extra characters allowed
    if i != |s| {
        return false;
    }
    return true;
}