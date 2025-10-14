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
    assert IsSorted(output);
    assert multiset(output) == multiset(input);
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := merge_sort(left);
    var rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
    // assert multiset(output) == multiset(input);
    // assert IsSorted(output);
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
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
    invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
    invariant (ai < |a| && bi < |b| ==> (|output| == 0 || output[|output|-1] <= a[ai] && output[|output|-1] <= b[bi]))
    invariant (ai < |a| && bi == |b| ==> (|output| == 0 || output[|output|-1] <= a[ai]))
    invariant (bi < |b| && ai == |a| ==> (|output| == 0 || output[|output|-1] <= b[bi]))
    decreases |a| - ai + |b| - bi
  {
    if ai == |a| {
      output := output + [b[bi]];
      bi := bi + 1;
    } else if bi == |b| {
      output := output + [a[ai]];
      ai := ai + 1;
    } else if a[ai] <= b[bi] {
      output := output + [a[ai]];
      ai := ai + 1;
    } else {
      output := output + [b[bi]];
      bi := bi + 1;
    }
  }
  assert ai == |a| && bi == |b|;
  assert multiset(output) == multiset(a) + multiset(b);
  assert IsSorted(output);
}

function merge_prefix(a:seq<int>, ai:int, b:seq<int>, bi:int): seq<int>
  requires 0 <= ai <= |a|
  requires 0 <= bi <= |b|
  decreases (|a| - ai) + (|b| - bi)
{
  if ai == |a| && bi == |b| then []
  else if ai == |a| {
    [b[bi]] + merge_prefix(a, ai, b, bi+1)
  } else if bi == |b| {
    [a[ai]] + merge_prefix(a, ai+1, b, bi)
  } else if a[ai] <= b[bi] {
    [a[ai]] + merge_prefix(a, ai+1, b, bi)
  } else {
    [b[bi]] + merge_prefix(a, ai, b, bi+1)
  }
}

method fast_sort(input:seq<int>) returns (output:seq<int>)
//  ensures SortSpec(input, output)
{
  output := [1, 2, 3];
}

function abs(a: real) : real {if a>0.0 then a else -a}
