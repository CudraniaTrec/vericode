
// Noa Leron 207131871
// Tsuri Farhana 315016907

ghost predicate ExistsSubstring(str1: string, str2: string) {
  exists offset :: 0 <= offset <= |str1| && str2 <= str1[offset..]
}

ghost predicate Post(str1: string, str2: string, found: bool, i: nat) {
  (found <==> ExistsSubstring(str1, str2)) &&
  (found ==> i + |str2| <= |str1| && str2 <= str1[i..])
}

method {:verify true} FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
  ensures Post(str1, str2, found, i)
{
  if |str2| == 0 {
    found, i := true, 0;
  }
  else if |str1| < |str2| {
    found, i := false, 0;
  }
  else {
    found, i := false, |str2|-1;

    while !found && i < |str1|
      invariant
        // If found, i points to a valid occurrence
        (found ==> i + |str2| <= |str1| && str2 <= str1[i..])
      invariant
        // If not found, no occurrence in str1[..i]
        (!found && i >= |str2| ==> forall k :: 0 <= k <= i - |str2| ==> !(str2 <= str1[k..]))
      invariant
        // i is always at least |str2|-1 and at most |str1|
        |str2|-1 <= i <= |str1|
      decreases |str1| - i
    {
      var j := |str2|-1;
      ghost var old_i := i;
      ghost var old_j := j;

      while !found && str1[i] == str2[j]
        invariant
          // j is in bounds
          0 <= j < |str2| && j <= i
        invariant
          // i is in bounds
          |str2|-1 <= i < |str1|
        invariant
          // If found, j==0 and str1[i]==str2[j]
          (found ==> j == 0 && str1[i] == str2[j])
        invariant
          // For all k in [j+1, |str2|), str1[i+k-j] == str2[k]
          forall k :: j < k < |str2| ==> str1[i + k - j] == str2[k]
        decreases j
      {
        if j == 0 {
          found := true;
        } else {
          i, j := i-1, j-1;
        }
      }

      if !found {
        // After the inner loop, if not found, then str1[i] != str2[j]
        // and all positions before i have been checked
        // Lemma1 is called for proof obligations
        Lemma1(str1, str2, i, j, old_i, old_j, found);

        i := old_i + (|str2| - (old_j - j));
      }
    }
  }
}

method Main() {
  var str1a, str1b := "string", " in Dafny is a sequence of characters (seq<char>)";
  var str1, str2 := str1a + str1b, "ring";
  var found, i := FindFirstOccurrence(str1, str2);
  print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
  if found {
    print " and i == ", i;
  }
  str1 := "<= on sequences is the prefix relation";
  found, i := FindFirstOccurrence(str1, str2);
  print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
  if found {
    print " and i == ", i;
  }
}

// Lemmas and predicates for verification

lemma {:verify true} Lemma1(str1: string, str2: string, i: nat, j: int, old_i: nat, old_j: nat, found: bool)
  requires !found
  requires |str2| > 0
  requires |str2|-1 <= old_i < |str1|
  requires |str2|-1 <= i < |str1|
  requires 0 <= j < |str2|
  requires old_j - j == old_i - i
  requires i + |str2| - j == old_i + 1
  requires str1[i] != str2[j]
  requires forall k :: 0 <= k <= old_i - |str2| ==> !(str2 <= str1[k..])
  ensures forall k :: 0 <= k <= old_i + 1 - |str2| ==> !(str2 <= str1[k..])
{
  // The only new possible substring is at offset old_i + 1 - |str2|, but str1[i] != str2[j] so it cannot match.
}


function abs(a: real) : real {if a>0.0 then a else -a}
