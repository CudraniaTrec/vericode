method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
{  
    var i := 0;
    var s: set<int> := {};
    while (i < |nums|)
        invariant 0 <= i <= |nums|
        invariant s == set nums[0..i]
        invariant forall j, k :: 0 <= j < k < i ==> nums[j] != nums[k]
    {
        var num := nums[i];
        if (num in s)
        {
            assert exists (j: int) :: 0 <= j < i && nums[j] == num;
            return false;
        }

        s := s + {num};
        i := i + 1;
    }

    assert forall j, k :: 0 <= j < k < |nums| ==> nums[j] != nums[k];
    return true;
}

predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}

function abs(a: real) : real {if a>0.0 then a else -a}
