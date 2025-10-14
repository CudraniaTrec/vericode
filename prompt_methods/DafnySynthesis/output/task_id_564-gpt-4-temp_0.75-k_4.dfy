method CountUnequalUnorderedPairs(a: seq<int>) returns (count: int)
  ensures 0 <= count <= |a| * (|a| - 1) / 2
  ensures forall i, j :: 0 <= i < j < |a| ==> ((a[i] != a[j]) ==> count >= 1)
{
  var n := |a|;
  var eqPairs := 0;
  // Count the frequency of each value
  var freq := map x: int {:auto_trigger} | x in a :: 0;
  for i := 0 to n - 1 {
    freq := freq[a[i] := if a[i] in freq then freq[a[i]] + 1 else 1];
  }
  // For each value, add number of equal unordered pairs
  var sumEqPairs := 0;
  for v in freq.Keys {
    var f := freq[v];
    sumEqPairs := sumEqPairs + f * (f - 1) / 2;
  }
  // Total unordered pairs
  var totalPairs := n * (n - 1) / 2;
  count := totalPairs - sumEqPairs;
}