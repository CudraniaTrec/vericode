method isDecimal(str: string) returns (res: bool)
{
    // A valid decimal with precision 2 must have at least 4 characters: "0.00"
    // There must be exactly one dot, and exactly two digits after the dot
    if |str| < 4 {
        res := false;
        return;
    }

    // Find the dot position
    var dotPos := -1;
    var dotCount := 0;
    var i := 0;
    while i < |str|
        decreases |str| - i
    {
        if str[i] == '.' {
            dotCount := dotCount + 1;
            if dotCount == 1 {
                dotPos := i;
            }
        }
        i := i + 1;
    }

    // There must be exactly one dot
    if dotCount != 1 {
        res := false;
        return;
    }

    // There must be exactly two digits after the dot
    if dotPos + 3 != |str| {
        res := false;
        return;
    }

    // All chars before dot must be digits
    var j := 0;
    while j < dotPos
        decreases dotPos - j
    {
        if str[j] < '0' || str[j] > '9' {
            res := false;
            return;
        }
        j := j + 1;
    }

    // The two chars after the dot must be digits
    if !(str[dotPos+1] >= '0' && str[dotPos+1] <= '9' && str[dotPos+2] >= '0' && str[dotPos+2] <= '9') {
        res := false;
        return;
    }

    res := true;
}