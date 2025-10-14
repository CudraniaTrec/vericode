method SumLengthsOfNamesStartingWithUppercase(names: seq<string>) returns (sum: int)
    ensures sum == sum([| name.Length | name <- names, |name| > 0 && 'A' <= name[0] <= 'Z' |])
{
    sum := 0;
    var n := names.Length;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant sum == sum([| names[j].Length | j <- 0 .. i, |names[j]| > 0 && 'A' <= names[j][0] <= 'Z' |])
    {
        if |names[i]| > 0 && 'A' <= names[i][0] <= 'Z' {
            sum := sum + names[i].Length;
        }
        i := i + 1;
    }
}