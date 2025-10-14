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
        invariant forall k, l :: 0 <= k < l < i ==> nums[k] != nums[l]
    {
        var num := nums[i];
        if (num in s)
        {
            result := false;
            return;
        }

        s := s + {num};
        i := i + 1;
    }

    result := true;
    return;
}

predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}

function abs(a: real) : real {if a>0.0 then a else -a}
