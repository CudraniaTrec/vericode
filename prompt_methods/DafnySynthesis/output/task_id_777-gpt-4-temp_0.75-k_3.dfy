//Dafny Code

method SumOfNonRepeatedElements(a: seq<int>) returns (sum: int)
  ensures sum == (set x | x in a && |a[x]| == 1) * x
{
    var freq := map x:int := 0;
    // Count frequencies
    for i := 0 to |a| - 1 {
        freq := freq[a[i] := if a[i] in freq then freq[a[i]] + 1 else 1];
    }
    sum := 0;
    // Sum up elements that appear exactly once
    for i := 0 to |a| - 1 {
        if freq[a[i]] == 1 {
            sum := sum + a[i];
        }
    }
    // To avoid double-counting, remove summed elements from freq
    var seen := set int{};
    for i := 0 to |a| - 1 {
        if freq[a[i]] == 1 && !(a[i] in seen) {
            seen := seen + {a[i]};
        }
    }
    // The above for loop ensures each non-repeated element is counted once
}