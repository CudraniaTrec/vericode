
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
		invariant 0 <= i < |q|
		invariant 0 <= j < |q|
		invariant i < j
		invariant Sorted(q)
		invariant HasAddends(q[i..j+1], x)
		decreases j - i
	{
		if (sum > x)
		{
			// Sum is too big, lower it by decreasing the high index
			LoopInvWhenSumIsBigger(q, x, i, j, sum);
			j := j - 1;
		}
		else // (sum < x)
		{
			i := i + 1;
		}
		sum := q[i] + q[j];
	}
	// After the loop, sum == x, i < j < |q|, so postcondition holds
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
	HasAddends(q[i..(j + 1)], x)
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
	requires HasAddends(q[i..j+1], x)
	ensures HasAddends(q[i..j], x)
{
	// If q[a] + q[j] == x for some a, then since q is sorted, q[a] <= q[i], so q[a] + q[j] <= q[i] + q[j] = sum > x, contradiction.
	// So any addends must be in q[i..j).
	assert forall a, b :: i <= a < b <= j && q[a] + q[b] == x ==> b < j;
	// So, HasAddends(q[i..j], x) holds.
	if exists a, b :: i <= a < b <= j && q[a] + q[b] == x {
		var a, b :| i <= a < b <= j && q[a] + q[b] == x;
		assert b < j;
		assert i <= a < b <= j-1;
		assert q[a] + q[b] == x;
	}
}

function abs(a: real) : real {if a>0.0 then a else -a}
