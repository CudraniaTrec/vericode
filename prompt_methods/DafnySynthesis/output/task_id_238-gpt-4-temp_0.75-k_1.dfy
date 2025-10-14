method CountNonEmptySubstrings(s: string) returns (count: int)
  ensures count == |s| * (|s| + 1) / 2
{
  var n := |s|;
  count := n * (n + 1) / 2;
}