// Dafny Code

method CanBeSumOfNonZeroPowersOf2(n: int) returns (res: bool)
    ensures res <==> (exists S: set<int> :: S != {} &&
                      (forall k :: k in S ==> k > 0) &&
                      (forall k1, k2 :: k1 in S && k2 in S && k1 != k2 ==> k1 != k2) &&
                      n == sum k | k in S :: 2 ^ k)
{
    if n <= 0 {
        // Only positive numbers can be written as sum of positive powers of 2
        return false;
    }
    // Remove the least significant 1 (if any) in the 2^0 place
    var m := n;
    if m % 2 == 1 {
        m := m - 1;
    }
    // Now, check if the remaining part can be written as sum of positive (k>0) powers of 2
    // That is, if m is a sum of 2^k for k>=1, i.e., no 1's in position 0
    // This is true if m is >= 0 and (m & 1) == 0
    // But, we already removed lowest bit

    // Now, m==0 means n was 1, which is 2^0. Only 2^0 is not allowed (since must be non-zero powers of 2)
    // So, n==1 should return false.

    // For n >= 2, we need to check that n can be written as a sum of 2^k for k>=1, i.e.,
    // n does not have any 1's in position 0.

    // To check this: n has at least one 1 in position >=1, i.e., n >> 1 != 0
    if (n >> 1) != 0 {
        // Now, need to check that n does not have any bits set except in positions >=1
        // i.e., all bits in position >=1 can be used any way (sum of 2^k, k>=1)
        // So, always possible unless n == 1
        return true;
    } else {
        return false;
    }
}