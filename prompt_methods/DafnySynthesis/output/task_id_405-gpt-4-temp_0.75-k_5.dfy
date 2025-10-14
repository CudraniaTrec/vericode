method Contains<T>(s: seq<T>, x: T) returns (exists: bool)
{
  exists := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant exists == (exists j :: 0 <= j < i && s[j] == x)
  {
    if s[i] == x {
      exists := true;
      break;
    }
    i := i + 1;
  }
}