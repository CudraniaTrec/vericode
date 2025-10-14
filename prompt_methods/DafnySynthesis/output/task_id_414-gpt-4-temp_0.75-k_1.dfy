method ExistsInSequence<T>(s: seq<T>, value: T) returns (existsInSeq: bool)
{
    existsInSeq := false;
    var i := 0;
    while i < |s| 
        invariant 0 <= i <= |s|
        invariant existsInSeq == (exists j :: 0 <= j < i && s[j] == value)
    {
        if s[i] == value {
            existsInSeq := true;
            break;
        }
        i := i + 1;
    }
}