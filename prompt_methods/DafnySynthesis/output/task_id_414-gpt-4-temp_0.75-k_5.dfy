method ExistsInSequence<T>(seq: seq<T>, value: T) returns (existsInSeq: bool)
{
    existsInSeq := false;
    var n := |seq|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant existsInSeq ==> (exists j :: 0 <= j < i && seq[j] == value)
        invariant !existsInSeq ==> (forall j :: 0 <= j < i ==> seq[j] != value)
    {
        if seq[i] == value {
            existsInSeq := true;
            break;
        }
        i := i + 1;
    }
}