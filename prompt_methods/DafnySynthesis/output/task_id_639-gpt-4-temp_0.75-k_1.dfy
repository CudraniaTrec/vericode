method SumLengthsOfNamesWithUppercaseStart(names: seq<string>) returns (total: nat)
    ensures total == sum(i | 0 <= i < |names| && |names[i]| > 0 && 'A' <= names[i][0] <= 'Z' :: |names[i]|)
{
    total := 0;
    var i := 0;
    while i < |names|
        invariant 0 <= i <= |names|
        invariant total == sum(j | 0 <= j < i && |names[j]| > 0 && 'A' <= names[j][0] <= 'Z' :: |names[j]|)
    {
        if |names[i]| > 0 && 'A' <= names[i][0] <= 'Z' {
            total := total + |names[i]|;
        }
        i := i + 1;
    }
}