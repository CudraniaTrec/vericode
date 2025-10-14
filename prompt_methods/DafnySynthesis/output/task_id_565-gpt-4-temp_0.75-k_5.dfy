method SplitIntoCharacters(s: string) returns (chars: seq<string>)
  ensures |chars| == |s|
  ensures forall i :: 0 <= i < |s| ==> chars[i] == s[i..i+1]
{
  var result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == s[j..j+1]
  {
    result := result + [s[i..i+1]];
    i := i + 1;
  }
  chars := result;
}