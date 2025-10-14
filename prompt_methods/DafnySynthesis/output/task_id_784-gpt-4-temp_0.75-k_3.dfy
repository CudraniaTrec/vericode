//Dafny Code

method ProductOfFirstEvenAndOdd(nums: seq<int>) returns (product: int)
  requires |nums| > 0
  ensures (exists i, j :: 0 <= i < |nums| && nums[i] % 2 == 0 &&
                      0 <= j < |nums| && nums[j] % 2 != 0) ==>
          product == nums[FirstEvenIndex(nums)][FirstOddIndex(nums)]
  ensures (forall i :: 0 <= i < |nums| ==> nums[i] % 2 != 0 ||
                                          nums[i] % 2 == 0) // vacuously true
{
  var evenFound := false;
  var oddFound := false;
  var firstEven := 0;
  var firstOdd := 0;

  var i := 0;
  while i < |nums| && !(evenFound && oddFound)
    invariant 0 <= i <= |nums|
    invariant evenFound ==> (exists j :: 0 <= j < i && nums[j] % 2 == 0)
    invariant oddFound ==> (exists j :: 0 <= j < i && nums[j] % 2 != 0)
  {
    if !evenFound && nums[i] % 2 == 0 {
      firstEven := nums[i];
      evenFound := true;
    }
    if !oddFound && nums[i] % 2 != 0 {
      firstOdd := nums[i];
      oddFound := true;
    }
    i := i + 1;
  }

  if evenFound && oddFound {
    product := firstEven * firstOdd;
  } else {
    // If not found, return 0 (or handle error as needed)
    product := 0;
  }
}

// Helper functions for specification only
function method FirstEvenIndex(nums: seq<int>): int
  requires exists i :: 0 <= i < |nums| && nums[i] % 2 == 0
{
  if nums[0] % 2 == 0 then 0 else 1 + FirstEvenIndex(nums[1..])
}

function method FirstOddIndex(nums: seq<int>): int
  requires exists i :: 0 <= i < |nums| && nums[i] % 2 != 0
{
  if nums[0] % 2 != 0 then 0 else 1 + FirstOddIndex(nums[1..])
}