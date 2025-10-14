method StartsAndEndsWithSameChar(s: string) returns (res: bool)
{
    if |s| == 0 {
        // For empty string, let's return false (could be true by convention, but here we choose false)
        res := false;
    } else {
        res := s[0] == s[|s| - 1];
    }
}