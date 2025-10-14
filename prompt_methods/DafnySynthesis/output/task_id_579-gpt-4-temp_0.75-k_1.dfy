// Dafny Code

method DissimilarElements(a: array<int>, b: array<int>) returns (result: set<int>)
  ensures result == (set x | (x in a[..] || x in b[..]) && !(x in a[..] && x in b[..]))
{
  var setA := set x | x in a[..];
  var setB := set x | x in b[..];
  result := (setA - setB) + (setB - setA);
}