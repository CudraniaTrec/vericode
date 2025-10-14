method MaxUppercaseRun(s: string) returns (maxRun: int)
{
    var currentRun := 0;
    maxRun := 0;
    var i := 0;
    while i < s.Length
        invariant 0 <= currentRun <= i+1
        invariant 0 <= maxRun <= i+1
        invariant 0 <= i <= s.Length
        invariant maxRun >= currentRun
    {
        if 'A' <= s[i] <= 'Z' {
            currentRun := currentRun + 1;
            if currentRun > maxRun {
                maxRun := currentRun;
            }
        } else {
            currentRun := 0;
        }
        i := i + 1;
    }
}