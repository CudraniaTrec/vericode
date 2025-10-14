
method Main()
{
	var q := [1,2,4,5,6,7,10,23];
	var i,j := FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i := 0;
	j := |q| - 1;
	var sum := q[i] + q[j];

	while sum != x
		invariant 0 <= i <= j < |q|
		invariant i < j
		invariant Sorted(q)
		invariant exists k, l :: i <= k < l <= j && q[k] + q[l] == x
		decreases j - i
	{
		if (sum > x)
		{
			// Sum is too big, lower it by decreasing the high index
			assert 0 <= i < j < |q|;
			LoopInvWhenSumIsBigger(q, x, i, j, sum);
			j := j - 1;
		}
		else // (sum < x)
		{
			// Sum is too small, make it bigger by increasing the low index.
			assert 0 <= i < j < |q|;
			LoopInvWhenSumIsSmaller(q, x, i, j, sum);
			i := i + 1;
		}
		assert 0 <= i < j < |q|;
		sum := q[i] + q[j];
	}
	assert 0 <= i < j < |q|;
	assert q[i] + q[j] == x;
}

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
	0 <= i < |q|
}

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
	0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
	q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j)
{
	exists k, l :: i <= k < l <= j && q[k] + q[l] == x
}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
	AreOreredIndices(q, i, j) &&
	HasAddendsInIndicesRange(q, x, i, j) &&
	AreAddendsIndices(q, sum, i, j)
}

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires HasAddends(q, x)
	requires Sorted(q)
	requires sum > x
	requires 0 <= i < j < |q|
	requires exists k, l :: i <= k < l <= j && q[k] + q[l] == x
	requires sum == q[i] + q[j]
	ensures exists k, l :: i <= k < l <= j-1 && q[k] + q[l] == x
{
	// Any addends (k,l) with q[k]+q[l]==x and l==j would have q[k]+q[j] <= q[i]+q[j] (since Sorted(q) and k >= i)
	// But q[i]+q[j] > x, so q[k]+q[j] <= q[i]+q[j] > x, so q[k]+q[j] > x or q[k]+q[j] < x, but not == x.
	// So any solution must have l < j.
	assert forall k, l :: i <= k < l <= j && q[k] + q[l] == x ==> l < j;
}

lemma LoopInvWhenSumIsSmaller(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires HasAddends(q, x)
	requires Sorted(q)
	requires sum < x
	requires 0 <= i < j < |q|
	requires exists k, l :: i <= k < l <= j && q[k] + q[l] == x
	requires sum == q[i] + q[j]
	ensures exists k, l :: i+1 <= k < l <= j && q[k] + q[l] == x
{
	// Any addends (k,l) with q[k]+q[l]==x and k==i would have q[i]+q[l] >= q[i]+q[j] (since Sorted(q) and l >= j)
	// But q[i]+q[j] < x, so q[i]+q[l] <= q[i]+q[j] < x, so q[i]+q[l] < x, so can't be == x.
	// So any solution must have k > i.
	assert forall k, l :: i <= k < l <= j && q[k] + q[l] == x ==> k > i;
}

function abs(a: real) : real {if a>0.0 then a else -a}
