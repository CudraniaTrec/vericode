// Dafny Code

method CanBeSumOfNonZeroPowersOf2(n: nat) returns (canRepresent: bool)
    ensures canRepresent <==> (exists S: set<int> :: S != {} && (forall k :: k in S ==> k > 0) && n == sum k | k in S :: 2^k)
{
    // Every number that can be written as the sum of non-zero powers of 2
    // can be written as the sum of distinct powers: i.e. the binary representation.
    // However, since "non-zero powers", we exclude 2^0 = 1, so only powers 2,4,8,...
    // That is, can we write n as a sum of 2^k for k >= 1 (i.e., 2,4,8,...)?
    //
    // So, remove as many 2^1, 2^2, ... as possible from n.
    // If after removing all such, we get 0, then it is possible.

    var m := n;
    while m > 0
        invariant 0 <= m <= n
        decreases m
    {
        if m >= 2 && m % 2 == 0 {
            // Remove the largest even power of 2 that divides m
            var pow := 1;
            while pow * 2 <= m
                invariant pow >= 1 && pow <= m
                decreases m - pow
            {
                pow := pow * 2;
            }
            m := m - pow;
        } else if m >= 2 && m % 2 == 1 {
            // For odd m >= 2, find the largest power of 2 less than m and subtract it
            var pow := 1;
            while pow * 2 <= m
                invariant pow >= 1 && pow <= m
                decreases m - pow
            {
                pow := pow * 2;
            }
            if pow == 1 {
                // 2^0 is not allowed
                return false;
            }
            m := m - pow;
        } else if m == 1 {
            // 2^0 is not allowed
            return false;
        } else {
            // m == 0
            return true;
        }
    }
    return true;
}