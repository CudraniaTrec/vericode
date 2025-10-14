method RemoveWhitespaces(s: string) returns (res: string)
  ensures |res| <= |s|
  ensures forall i :: 0 <= i < |res| ==> res[i] != ' '
  ensures forall i :: 0 <= i < |s| && s[i] != ' ' ==> exists j :: 0 <= j < |res| && res[j] == s[i]
{
  var sb := new seq<char>[];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sb| <= i
    invariant forall j :: 0 <= j < |sb| ==> sb[j] != ' '
    invariant forall k :: 0 <= k < i && s[k] != ' ' ==> exists j :: 0 <= j < |sb| && sb[j] == s[k]
  {
    if s[i] != ' ' {
      sb := sb + [s[i]];
    }
    i := i + 1;
  }
  res := StringFromCharArray(sb);
}