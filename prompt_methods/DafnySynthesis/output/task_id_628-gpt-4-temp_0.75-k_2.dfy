method ReplaceSpacesWithPercent20(s: string) returns (res: string)
  ensures res == s.Replace(" ", "%20")
{
  var sb := new seq<char>[];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sb| == i
    invariant forall j :: 0 <= j < i ==> 
      if s[j] == ' ' then sb[j] == '%' && sb[j+1] == '2' && sb[j+2] == '0'
      else sb[j] == s[j]
  {
    if s[i] == ' ' {
      sb := sb + ['%', '2', '0'];
    } else {
      sb := sb + [s[i]];
    }
    i := i + 1;
  }
  res := string(sb);
}