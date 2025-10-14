method ToUpperCase(s: string) returns (upper: string)
{
  var chars: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |chars| == i
    decreases |s| - i
  {
    var c := s[i];
    if 'a' <= c <= 'z' {
      // Convert lowercase to uppercase by offset
      chars := chars + [(c as int - ('a' as int) + ('A' as int)) as char];
    } else {
      chars := chars + [c];
    }
    i := i + 1;
  }
  upper := chars[..];
}