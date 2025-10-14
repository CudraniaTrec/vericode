method SplitStringIntoChars(s: string) returns (chars: seq<char>)
  ensures |chars| == s.Length
  ensures forall i :: 0 <= i < s.Length ==> chars[i] == s[i]
{
  var result := [];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant result == [s[j] | j := 0 .. i]
  {
    result := result + [s[i]];
    i := i + 1;
  }
  chars := result;
}