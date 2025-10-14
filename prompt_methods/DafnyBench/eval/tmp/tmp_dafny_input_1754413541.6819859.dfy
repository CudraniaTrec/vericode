
function sum(nums: seq<int>): int {
    if |nums| == 0 then 0 else sum(nums[0..(|nums|-1)])+nums[|nums|-1]
}

function sumUp(nums: seq<int>): int {
    if |nums| == 0 then 0 else nums[0]+sumUp(nums[1..])
}

// By Divyanshu Ranjan
lemma sumUpLemma(a: seq<int>, b: seq<int>)
  ensures sumUp(a + b) == sumUp(a) + sumUp(b)
{
  if a == [] {
  }
  else {
    sumUpLemma(a[1..], b);
    calc {
      sumUp(a + b);
      {
      }
      a[0] + sumUp(a[1..] + b);
      a[0] + sumUp(a[1..]) + sumUp(b);
    }
  }
}

// By Divyanshu Ranjan
lemma sumsEqual(nums: seq<int>)
  ensures sum(nums) == sumUp(nums)
{
  if nums == [] {}
  else {
    var ln := |nums|-1;
    calc {
      sumUp(nums[..]);
      {
        sumUpLemma(nums[0..ln], [nums[ln]]);
      }
      sumUp(nums[0..ln]) + sumUp([nums[ln]]);
      {
      }
      sumUp(nums[0..ln]) + nums[ln];
      {
        sumsEqual(nums[0..ln]);
      }
      sum(nums[0..ln]) + nums[ln];
    }
  }
}

method  FindPivotIndex(nums: seq<int>) returns (index: int)
    requires |nums| > 0
    ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
{
    var n := |nums|;
    var leftsums: seq<int> := [0];
    var i := 0;
    // leftsums[i] = sum(nums[0..i])
    while i < n
        invariant 0 <= i <= n
        invariant |leftsums| == i+1
        invariant leftsums[0] == 0
        invariant forall j: int :: 0 <= j <= i ==> leftsums[j] == sum(nums[0..j])
    {
        leftsums := leftsums + [leftsums[i] + nums[i]];
        i := i + 1;
    }
    var rightsum := sum(nums);
    i := 0;
    var leftsum := 0;
    while i < n
        invariant 0 <= i <= n
        invariant leftsum == sum(nums[0..i])
        invariant rightsum == sum(nums)
        invariant forall k: int :: 0 <= k < i ==> leftsum - nums[k] != sum(nums[(k+1)..])
    {
        // leftsum = sum(nums[0..i])
        // rightsum = sum(nums)
        // sum(nums[(i+1)..]) = rightsum - leftsum - nums[i] + nums[i] = rightsum - leftsum
        // Actually, sum(nums[(i+1)..]) = rightsum - leftsum - nums[i]
        var rights := rightsum - leftsum - nums[i];
        if leftsum == rights {
            index := i;
            return;
        }
        leftsum := leftsum + nums[i];
        i := i + 1;
    }
    index := -1;
    return;
}

function abs(a: real) : real {if a>0.0 then a else -a}
