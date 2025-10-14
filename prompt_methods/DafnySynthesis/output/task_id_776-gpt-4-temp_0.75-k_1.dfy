//Dafny Code

method CountCharsWithVowelNeighbors(s: string) returns (count: int)
{
  var vowels := set {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'};
  count := 0;
  var n := s.Length;
  if n == 0 {
    return;
  }
  for i := 0 to n - 1
    invariant 0 <= count <= i + 1
    invariant 0 <= i <= n
  {
    var hasVowelNeighbor := false;
    if i > 0 && s[i-1] in vowels {
      hasVowelNeighbor := true;
    }
    if i < n - 1 && s[i+1] in vowels {
      hasVowelNeighbor := true;
    }
    if hasVowelNeighbor {
      count := count + 1;
    }
  }
}