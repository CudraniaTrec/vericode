//Dafny Code

method ExtractRearChars(strings: seq<string>) returns (rears: seq<char>)
  ensures |rears| == |strings|
  ensures forall i :: 0 <= i < |strings| ==> (|strings[i]| > 0 ==> rears[i] == strings[i][|strings[i]|-1])
{
  var result := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (|strings[j]| > 0 ==> result[j] == strings[j][|strings[j]|-1])
  {
    if |strings[i]| > 0 {
      result := result + [strings[i][|strings[i]|-1]];
    } else {
      // In case of empty string, append an arbitrary char (could also throw an error or use option type)
      result := result + ['\0'];
    }
    i := i + 1;
  }
  rears := result;
}