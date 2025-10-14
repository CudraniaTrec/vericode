method MaxUppercaseRun(s: string) returns (maxRun: int)
{
    var n := s.Length;
    var currRun := 0;
    maxRun := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= currRun <= i
        invariant 0 <= maxRun <= i
    {
        if 'A' <= s[i] <= 'Z' {
            currRun := currRun + 1;
            if currRun > maxRun {
                maxRun := currRun;
            }
        } else {
            currRun := 0;
        }
        i := i + 1;
    }
}