//Dafny Code

method ContainsZ(word: string) returns (result: bool)
{
  result := false;
  var i := 0;
  while i < |word|
    invariant 0 <= i <= |word|
    invariant result == (exists j :: 0 <= j < i && word[j] == 'z')
  {
    if word[i] == 'z' {
      result := true;
      break;
    }
    i := i + 1;
  }
  // After loop: result is true if 'z' was found, else false
}