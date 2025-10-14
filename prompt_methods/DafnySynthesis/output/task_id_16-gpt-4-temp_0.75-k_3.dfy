method HasLowercaseUnderscoreSequences(s: string) returns (res: bool)
{
  // We look for a substring matching: one or more lowercase letters,
  // followed by an underscore, followed by one or more lowercase letters.
  var i := 0;
  res := false;
  while i < s.Length - 2 // At least 3 chars needed for a match
    invariant 0 <= i <= s.Length
    invariant !res ==> (forall j :: 0 <= j < i ==> 
      // No match starts at position j
      !(IsLowercase(s[j]) && ExistsSequence(s, j))
    )
  {
    if IsLowercase(s[i]) {
      // Find a maximal run of lowercase letters starting at i
      var start := i;
      while i < s.Length && IsLowercase(s[i]) 
        decreases s.Length - i
      {
        i := i + 1;
      }
      var endOfFirstSeq := i;
      // Now, s[start .. endOfFirstSeq) is all lowercase, and i points to non-lowercase or end
      if i < s.Length && s[i] == '_' {
        var underscore := i;
        i := i + 1;
        var secondSeqStart := i;
        // Check if there is at least one lowercase letter after the underscore
        if i < s.Length && IsLowercase(s[i]) {
          while i < s.Length && IsLowercase(s[i]) 
            decreases s.Length - i
          {
            i := i + 1;
          }
          // We found: lowercase letters, underscore, lowercase letters
          res := true;
          return;
        }
      }
    } else {
      i := i + 1;
    }
  }
}

function IsLowercase(c: char): bool
{
  'a' <= c <= 'z'
}

// Helper predicate to express that from position j there is a sequence as described
predicate ExistsSequence(s: string, j: int)
{
  // There exists k > j+1 such that s[j..k) are lowercase, s[k] == '_', s[k+1] is lowercase
  exists k, l :: 
    j < k < s.Length - 1 &&
    (forall x :: j <= x < k ==> IsLowercase(s[x])) &&
    s[k] == '_' &&
    IsLowercase(s[k+1])
}