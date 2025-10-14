method RemoveWordsOfLengthK(s: string, k: nat) returns (result: string)
  ensures forall word :: word in result.Split(" ") ==> |word| != k
{
  var words := s.Split(" ");
  var filteredWords := new seq<string>([]);
  // Filter out words of length k
  var i := 0;
  while i < |words|
    invariant 0 <= i <= |words|
    invariant filteredWords == [words[j] | j :: 0 <= j < i && |words[j]| != k]
  {
    if |words[i]| != k {
      filteredWords := filteredWords + [words[i]];
    }
    i := i + 1;
  }
  // Join filtered words with spaces
  if |filteredWords| == 0 {
    result := "";
  } else {
    result := filteredWords[0];
    var j := 1;
    while j < |filteredWords|
      invariant 1 <= j <= |filteredWords|
      invariant result == String.Join(" ", filteredWords[..j])
    {
      result := result + " " + filteredWords[j];
      j := j + 1;
    }
  }
}