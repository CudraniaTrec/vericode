//Dafny Code

method ListDifference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
  ensures diff == a - b
{
  // Using Dafny's set difference operator (-), but lists are sequences.
  // So, we build diff as all elements in 'a' not in 'b', preserving order and duplicates.
  var result := [];
  var b_counts := map x | x in b :: |b[x]|;
  var seen := map x:int := 0;

  // For each element in 'a', if we've not already skipped as many as in 'b', skip it, else include it.
  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant |result| <= i
    invariant forall j :: 0 <= j < |result| ==> result[j] in a
  {
    var x := a[i];
    if seen[x] < (if x in b_counts then b_counts[x] else 0) {
      seen[x] := seen[x] + 1;
      // skip this occurrence
    } else {
      result := result + [x];
    }
  }
  diff := result;
}