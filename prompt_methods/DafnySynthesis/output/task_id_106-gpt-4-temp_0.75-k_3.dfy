method AppendArrayToSequence<T>(s: seq<T>, a: array<T>) returns (result: seq<T>)
    ensures result == s + a[..]
{
    var arrSeq := a[..];
    result := s + arrSeq;
}