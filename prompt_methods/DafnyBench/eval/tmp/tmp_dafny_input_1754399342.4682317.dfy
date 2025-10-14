
method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
{
  prefix := [];
  var minLength := if |str1| <|str2| then |str1| else |str2|;

  var idx: int := 0;
  while idx < minLength
    invariant 0 <= idx <= minLength
    invariant prefix == str1[0..idx] && prefix == str2[0..idx]
    invariant |prefix| == idx
    invariant |prefix| <= |str1| && |prefix| <= |str2|
  {
    if str1[idx] != str2[idx] {
      return;
    }
    prefix := prefix + [str1[idx]];
    idx := idx + 1;
  }
  // After the loop, idx == minLength
  // Check if we stopped because we reached the end of one of the strings
  // The ensures will be satisfied because either |prefix| == |str1| or |prefix| == |str2| or str1[|prefix|] != str2[|prefix|]
  // But at this point, idx == minLength, so prefix == str1[0..minLength] == str2[0..minLength]
  // and |prefix| == minLength
  // No further action needed
}

function abs(a: real) : real {if a>0.0 then a else -a}
