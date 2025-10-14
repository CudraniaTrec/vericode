method countSamePair(l1: seq<int>, l2: seq<int>, l3: seq<int>) returns (res: int)
{
    var n := |l1|;
    res := 0;
    var m := if |l2| < n then |l2| else n;
    m := if |l3| < m then |l3| else m;

    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant res == (|set j | 0 <= j < i && l1[j] == l2[j] && l2[j] == l3[j]|)
    {
        if l1[i] == l2[i] && l2[i] == l3[i] {
            res := res + 1;
        }
        i := i + 1;
    }
}