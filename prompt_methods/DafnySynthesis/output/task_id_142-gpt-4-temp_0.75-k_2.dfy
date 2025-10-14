method countSamePair(l1: seq<int>, l2: seq<int>, l3: seq<int>) returns (res: int)
{
    var minLen := if |l1| < |l2| then (if |l1| < |l3| then |l1| else |l3|) else (if |l2| < |l3| then |l2| else |l3|);
    res := 0;
    var i := 0;
    while i < minLen
        invariant 0 <= i <= minLen
        invariant res == (sum j | 0 <= j < i :: if l1[j] == l2[j] && l1[j] == l3[j] then 1 else 0)
    {
        if l1[i] == l2[i] && l1[i] == l3[i] {
            res := res + 1;
        }
        i := i + 1;
    }
}