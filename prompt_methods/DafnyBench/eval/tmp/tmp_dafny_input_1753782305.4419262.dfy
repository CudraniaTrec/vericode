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
        (found ==> i + |str2| <= |str1| && str2 <= str1[i..])
      invariant
        (!found && i >= |str2|-1 ==> forall k :: 0 <= k <= i - |str2| ==> !(str2 <= str1[k..]))
      invariant
        |str2|-1 <= i <= |str1|
      decreases |str1| - i
    {
      var j := |str2|-1;
      var i0 := i;
      var j0 := j;

      while !found && str1[i] == str2[j]
        invariant 0 <= j < |str2| && j <= i
        invariant |str2|-1 <= i < |str1|
        invariant (found ==> j == 0 && str1[i] == str2[j])
        invariant forall k :: j < k < |str2| ==> str1[i + k - j] == str2[k]
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
        // and all positions before i0 have been checked
        // Lemma1 is called for proof obligations
        Lemma1(str1, str2, i, j, i0, j0, found);

        i := i0 + (|str2| - (j0 - j));
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

lemma {:verify true} Lemma1(str1: string, str2: string, i: nat, j: int, i0: nat, j0: int, found: bool)
  requires !found
  requires |str2| > 0
  requires |str2|-1 <= i0 < |str1|
  requires |str2|-1 <= i < |str1|
  requires 0 <= j < |str2|
  requires j0 - j == i0 - i
  requires i + |str2| - j == i0 + 1
  requires str1[i] != str2[j]
  requires forall k :: 0 <= k <= i0 - |str2| ==> !(str2 <= str1[k..])
  ensures forall k :: 0 <= k <= i0 + 1 - |str2| ==> !(str2 <= str1[k..])
{
  // The only new possible substring is at offset i0 + 1 - |str2|, but str1[i] != str2[j] so it cannot match.
}


function abs(a: real) : real {if a>0.0 then a else -a}
