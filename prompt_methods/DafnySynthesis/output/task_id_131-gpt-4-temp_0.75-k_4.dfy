method ReverseVowels(s: string) returns (res: string)
{
  var chars := s.ToCharArray();
  var n := chars.Length;
  var vowels := set ['a','e','i','o','u','A','E','I','O','U'];

  var i := 0;
  var j := n - 1;
  while i < j
    decreases j - i
  {
    while i < j && !(chars[i] in vowels)
      decreases j - i
    {
      i := i + 1;
    }
    while i < j && !(chars[j] in vowels)
      decreases j - i
    {
      j := j - 1;
    }
    if i < j {
      var temp := chars[i];
      chars[i] := chars[j];
      chars[j] := temp;
      i := i + 1;
      j := j - 1;
    }
  }
  res := string(chars);
}