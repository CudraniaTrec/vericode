method AppendArrayToSeq<T>(s: seq<T>, a: array<T>) returns (r: seq<T>)
    requires a != null
    ensures r == s + a[..]
{
    r := s + a[..];
}