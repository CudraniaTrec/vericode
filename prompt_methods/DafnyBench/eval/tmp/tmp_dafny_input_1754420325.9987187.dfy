
predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}

//lemma SequenceConcat(s:seq<int>, pivot:int)
//  requires 0<=pivot<|s|
//  ensures s[..pivot] + s[pivot..] == s
//{
//}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := left;
    leftSorted := merge_sort(left);
    var rightSorted := right;
    rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
    //    calc {
    //      multiset(output);
    //      multiset(leftSorted + rightSorted);
    //      multiset(leftSorted) + multiset(rightSorted);
    //      multiset(left) + multiset(right);
    //      multiset(left + right);
    //        { assert left + right == input; }
    //      multiset(input);
    //    }
  }
}

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures SortSpec(a+b, output)
  decreases |a|+|b|
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    invariant 0 <= ai <= |a|
    invariant 0 <= bi <= |b|
    invariant |output| == ai + bi
    invariant output == merge_prefix(a, ai, b, bi)
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
    invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
    invariant forall i :: 0 <= i < ai ==> (i == 0 || a[i-1] <= a[i])
    invariant forall i :: 0 <= i < bi ==> (i == 0 || b[i-1] <= b[i])
    invariant (ai < |a| ==> (|output| == 0 || output[|output|-1] <= a[ai]))
    invariant (bi < |b| ==> (|output| == 0 || output[|output|-1] <= b[bi]))
  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
    }
    //    calc {
    //      multiset(a[..ai]) + multiset(b[..bi]);
    //      multiset(a[..ao] + a[ao..ai]) + multiset(b[..bo] + b[bo..bi]);
    //      multiset(a[..ao]) + multiset(a[ao..ai]) + multiset(b[..bo]) + multiset(b[bo..bi]);
    //      multiset(a[..ao]) + multiset(b[..bo]) + multiset(a[ao..ai]) + multiset(b[bo..bi]);
    //      multiset(outputo) + multiset(a[ao..ai]) + multiset(b[bo..bi]);
    //      multiset(output);
    //    }
  }
  //  calc {
  //    multiset(output);
  //    multiset(a[..ai]) + multiset(b[..bi]);
  //    multiset(a) + multiset(b);
  //    multiset(a + b);
  //  }
  assert ai == |a| && bi == |b|;
  assert multiset(output) == multiset(a) + multiset(b);
  assert IsSorted(output);
}

function method merge_prefix(a:seq<int>, ai:int, b:seq<int>, bi:int): seq<int>
  decreases |a| - ai + |b| - bi
{
  if ai == |a| && bi == |b| then []
  else if ai == |a| || (bi < |b| && a[ai] > b[bi]) then
    [b[bi]] + merge_prefix(a, ai, b, bi+1)
  else
    [a[ai]] + merge_prefix(a, ai+1, b, bi)
}

method fast_sort(input:seq<int>) returns (output:seq<int>)
//  ensures SortSpec(input, output)
{
  output := [1, 2, 3];
}

function abs(a: real) : real {if a>0.0 then a else -a}
