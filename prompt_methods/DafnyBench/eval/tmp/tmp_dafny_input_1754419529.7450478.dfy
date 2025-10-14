method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
{
    var previous := nums[0];
    result := [nums[0]];

    var i := 1;
    while (i < |nums|)
        invariant 1 <= i <= |nums|
        invariant result == [nums[0]] + (seq j | 1 <= j < i && nums[j] != nums[j-1] :: nums[j])
        invariant previous == nums[i-1]
        invariant is_sorted_and_distinct(result)
        invariant forall k :: 0 <= k < i ==> nums[k] in result
        invariant forall x :: x in result ==> x in nums[..i]
    {
        if (previous != nums[i])
        { 
            result := result + [nums[i]];
            previous := nums[i];
        }

        i := i + 1;
    }
}


// Helper predicate
predicate is_sorted(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
}

predicate is_sorted_and_distinct(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] < nums[j]
}

function abs(a: real) : real {if a>0.0 then a else -a}
