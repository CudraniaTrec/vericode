
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
    var rightsums: seq<int> := [0];
    var i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant |leftsums| == i
        invariant |rightsums| == i
        invariant leftsums[0] == 0
        invariant rightsums[0] == 0
        invariant forall j: int :: 0 <= j < i ==> leftsums[j] == sum(nums[0..j])
        invariant forall j: int :: 0 <= j < i ==> rightsums[j] == sum(nums[(n-j)..])
    {
        leftsums := leftsums + [leftsums[i-1]+nums[i-1]];
        rightsums := rightsums + [nums[n-i]+rightsums[i-1]];
        i := i + 1;
    }

    // Prove rightsums[k] == sum(nums[(n-k)..]) for all k
    forall k: nat | 0 <= k < |rightsums| && k <= n
        ensures rightsums[k] == sum(nums[(n-k)..])
    {
        // By loop invariant above, this holds
    }

    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j: int :: 0 <= j < i ==> leftsums[j] != rightsums[n-(j+1)]
        invariant |leftsums| == n+1
        invariant |rightsums| == n+1
    {
        var x := n-(i+1);
        // leftsums[i] == sum(nums[0..i])
        // rightsums[x] == sum(nums[(n-x)..]) == sum(nums[i..])
        if leftsums[i] == rightsums[x] {
            // sum(nums[0..i]) == sum(nums[i..])
            // But we want sum(nums[0..i]) == sum(nums[(i+1)..])
            // sum(nums[i..]) = nums[i] + sum(nums[(i+1)..])
            // So sum(nums[0..i]) == nums[i] + sum(nums[(i+1)..])
            // So sum(nums[0..i]) - nums[i] == sum(nums[(i+1)..])
            // But the problem wants sum(nums[0..index]) == sum(nums[(index+1)..])
            // So this is not the same unless nums[i] == 0
            // Instead, we should check sum(nums[0..i]) == sum(nums[(i+1)..])
            if sum(nums[0..i]) == sum(nums[(i+1)..]) {
                return i;
            }
        }
        i := i + 1;
    }
    return -1;
}

function abs(a: real) : real {if a>0.0 then a else -a}
