method ReverseEachString(strings: seq<string>) returns (reversed: seq<string>)
  ensures |reversed| == |strings|
  ensures forall i :: 0 <= i < |strings| ==> reversed[i] == strings[i][..][::-1]
{
  var result := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == strings[j][..][::-1]
  {
    var s := strings[i];
    var rev := "";
    var j := |s| - 1;
    while j >= 0
      invariant -1 <= j < |s|
      invariant |rev| == |s| - 1 - j
      invariant rev == s[j+1..][::-1]
    {
      rev := rev + s[j..j+1];
      j := j - 1;
    }
    result := result + [rev];
    i := i + 1;
  }
  reversed := result;
}