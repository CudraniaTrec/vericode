method ArrayToSeq<A>(a: array<A>) returns (s: seq<A>)
  ensures s == a[..]
{
  s := a[..];
}