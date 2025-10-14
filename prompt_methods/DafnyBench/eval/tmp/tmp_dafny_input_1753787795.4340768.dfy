
predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
    pair := (0,0);
    var i: nat := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant forall x:nat, y:nat :: x < y < i ==> !summingPair(x, y, nums, target)
    {
        var k: nat := i + 1;
        while k < |nums|
            invariant i + 1 <= k <= |nums|
            invariant forall y:nat :: i + 1 <= y < k ==> !summingPair(i, y, nums, target)
            invariant forall x:nat, y:nat :: x < y < i ==> !summingPair(x, y, nums, target)
        {
            // assert i < k < |nums|;
            if nums[i] + nums[k] == target {
                pair := (i,k);
                // assert summingPair(pair.0, pair.1, nums, target);
                return pair;
            }
            k := k + 1;
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
