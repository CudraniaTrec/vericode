// Dafny Code

method MinLengthSublist(s: seq<seq<int>>) returns (minSub: seq<int>)
    ensures minSub in s || |s| == 0
    ensures forall x :: x in s ==> |minSub| <= |x|
{
    if |s| == 0 {
        // Return the empty sequence if input is empty
        minSub := [];
        return;
    }
    var minIdx := 0;
    var minLen := |s[0]|;
    var i := 1;
    while i < |s|
        invariant 1 <= |s| ==> 0 <= minIdx < |s|
        invariant forall j :: 0 <= j < i ==> |s[minIdx]| <= |s[j]|
        decreases |s| - i
    {
        if |s[i]| < minLen {
            minLen := |s[i]|;
            minIdx := i;
        }
        i := i + 1;
    }
    minSub := s[minIdx];
}