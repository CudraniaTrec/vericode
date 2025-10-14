method ReverseStrings(lst: seq<string>) returns (reversed: seq<string>)
  ensures |reversed| == |lst|
  ensures forall i :: 0 <= i < |lst| ==> reversed[i] == lst[i][..][-|1..0] // reversed string
{
  reversed := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant |reversed| == i
    invariant forall j :: 0 <= j < i ==> reversed[j] == lst[j][..][-|1..0]
  {
    // Reverse lst[i]:
    var s := lst[i];
    var rev := "";
    var j := |s| - 1;
    while j >= 0
      invariant -1 <= j < |s|
      invariant |rev| == |s| - 1 - j
      invariant rev == s[|s|-1..j+1:-1]
    {
      rev := rev + s[j..j+1];
      j := j - 1;
    }
    reversed := reversed + [rev];
    i := i + 1;
  }
}