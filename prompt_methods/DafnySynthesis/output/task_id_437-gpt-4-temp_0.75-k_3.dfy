method RemoveOddCharacters(s: string) returns (result: string)
{
  var chars := new seq<char>([]);
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant chars == (seq j | 0 <= j < i && j % 2 == 0 :: s[j])
  {
    if i % 2 == 0 {
      chars := chars + [s[i]];
    }
    i := i + 1;
  }
  result := chars[..];
}