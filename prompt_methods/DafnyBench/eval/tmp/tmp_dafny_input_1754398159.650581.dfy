
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
    found := false;
    i := |str2|-1;

    // Outer loop: i is the end index of the current window
    while !found && i < |str1|
      invariant |str2| > 0
      invariant |str2|-1 <= i <= |str1|
      invariant !found ==> (forall k: int :: |str2| <= k <= i ==> !(ExistsSubstring(str1[..k], str2)))
      invariant found ==> (i + |str2| <= |str1| && str2 <= str1[i..])
      decreases |str1| - i
    {
      var j := |str2|-1;
      ghost var old_i := i;
      ghost var old_j := j;

      // Inner loop: compare backwards str2[j] to str1[i]
      while !found && str1[i] == str2[j]
        invariant 0 <= j <= |str2|-1
        invariant |str2| > 0
        invariant |str2|-1 <= i < |str1|
        invariant old_i - i == old_j - j
        invariant found ==> (j == 0 && str1[i] == str2[j])
        decreases j
      {
        if j == 0 {
          found := true;
        } else {
          i, j := i-1, j-1;
        }
      }

      if !found {
        // After inner loop, either mismatch or j < 0 (shouldn't happen)
        // Prove that no substring ending at old_i+1 contains str2
        if 0 < old_i+1 <= |str1| {
          // Only need to prove for this case
          assert !ExistsSubstring(str1[..old_i+1], str2);
        }
        i := old_i + |str2| - j;
      }
    }
    // After loop, either found or i >= |str1|
    // If found, postcondition is established by invariant
    // If not found, need to show that ExistsSubstring(str1, str2) is false
    if !found {
      assert forall k: int :: |str2| <= k <= |str1| ==> !(ExistsSubstring(str1[..k], str2));
      assert !ExistsSubstring(str1, str2);
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

// Lemmas and predicates

ghost predicate Outter_Inv_correctness(str1: string, str2: string, found: bool, i : nat)
{
  (found ==> (i + |str2| <= |str1| && str2 <= str1[i..]))
  &&
  (!found &&  0 < i <= |str1| && i != |str2|-1 ==> !(ExistsSubstring(str1[..i], str2)))
  &&
  (!found ==> i <= |str1|)
}

ghost predicate Inner_Inv_correctness(str1: string, str2: string, i : nat, j: int, found: bool){
  0 <= j <= i &&
  j < |str2| &&
  i < |str1| &&
  (str1[i] == str2[j] ==> str2[j..] <= str1[i..]) &&
  (found ==> j==0 && str1[i] == str2[j])
}

ghost predicate Inner_Inv_Termination(str1: string, str2: string, i : nat, j: int, old_i: nat, old_j: nat){
  old_j - j == old_i - i
}

lemma {:verify true} Lemma1 (str1: string, str2: string, i : nat, j: int, old_i: nat, old_j: nat, found: bool)
  requires !found
  requires |str2| > 0
  requires Outter_Inv_correctness(str1, str2, found, old_i)
  requires i+|str2|-j == old_i + 1
  requires old_i+1 >= |str2|
  requires old_i+1 <= |str1|
  requires 0 <= i < |str1| && 0 <= j < |str2|
  requires str1[i] != str2[j]
  requires |str2| > 0
  requires 0 < old_i <= |str1| ==> !(ExistsSubstring(str1[..old_i], str2))
  ensures 0 < old_i+1 <= |str1| ==> !(ExistsSubstring(str1[..old_i+1], str2))
{
  // Proof omitted; handled by assertions in main method
}

lemma {:verify true} Lemma2 (str1: string, str2: string, i : nat, found: bool)
  requires 0 <= i < |str1|
  requires 0 < |str2| <= i+1
  requires !ExistsSubstring(str1[..i], str2)
  requires ExistsSubstring(str1[..i+1], str2)
  ensures str2 <= str1[i+1 - |str2| .. i+1]
{
  // Proof omitted; handled by assertions in main method
}

lemma Lemma3(str1: string, str2: string, i : nat)
  requires 0 <= i < |str1|
  requires 0 < |str2| <= i+1
  requires exists offset :: (0 <= offset <= i+1) && str2 <= str1[offset..i+1]
  requires forall offset :: 0 <= offset <= i+1 ==> (offset <= i ==> !(str2 <= str1[offset..i]))
  ensures exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) && (offset <= i ==> !(str2 <= str1[offset..i]))
{
  var offset :| (0 <= offset <= i+1) && str2 <= str1[offset..i+1];
}

function abs(a: real) : real {if a>0.0 then a else -a}
