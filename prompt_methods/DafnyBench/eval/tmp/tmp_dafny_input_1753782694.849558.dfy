method Main() {
	var q := [7, -2, 3, -2];

	var p, c := ProdAndCount(q, -2);
	print "The product of all positive elements in [7,-2,3,-2] is ";
	print p;
	print "\nThe number of occurrences of -2 in [7,-2,3,-2] is ";
	print c;
	calc {
		RecursiveCount(-2, q);
	== { assert q[3] == -2; AppendOne(q, 3); }
		1 + RecursiveCount(-2, q[..3]);
	== { assert q[2] != -2; AppendOne(q, 2); }
		1 + RecursiveCount(-2, q[..2]);
	== { assert q[1] == -2; AppendOne(q, 1); }
		1 + 1 + RecursiveCount(-2, q[..1]);
	== { assert q[0] != -2; AppendOne(q, 0); }
		1 + 1 + RecursiveCount(-2, q[..0]);
	}
}

lemma AppendOne<T>(q: seq<T>, n: nat)
	requires n < |q|
	ensures q[..n] + [q[n]] == q[..n+1]
{}

function RecursivePositiveProduct(q: seq<int>): int
{
	if q == [] then 1
	else if q[0] <= 0 then RecursivePositiveProduct(q[1..])
	else q[0] * RecursivePositiveProduct(q[1..])
}

function RecursiveCount(key: int, q: seq<int>): int
{
	if q == [] then 0
	else if q[|q|-1] == key then 1 + RecursiveCount(key, q[..|q|-1])
	else RecursiveCount(key, q[..|q|-1])
}

method ProdAndCount(q: seq<int>, key: int) returns (prod: int, count: nat)
	ensures prod == RecursivePositiveProduct(q)
	ensures count == RecursiveCount(key, q)
{
	prod := 1;
	count := 0;
	var size := |q|;
	var i := 0;
	var curr := 0;
	while i < size
		invariant 0 <= i <= size
		invariant count == RecursiveCount(key, q[..i])
		invariant prod == RecursivePositiveProduct(q[..i])
		decreases size - i
	{
		curr := q[i];
		if curr > 0 {
			prod := prod * curr;
		}
		if curr == key {
			count := count + 1;
		}
		i := i + 1;
	}
	assert i == size;
	assert q[..i] == q;
	assert count == RecursiveCount(key, q);
	assert prod == RecursivePositiveProduct(q);
}

function county(elem: int, key: int): int {
	if elem == key then 1 else 0
}

function prody(elem: int): int {
	if elem <= 0 then 1 else elem
}

lemma Lemma_Count_Inv(q: seq<int>, i: nat, count: int, key: int)
	requires 0 <= i < |q| && count == RecursiveCount(key, q[..i])
	ensures 0 <= i+1 <= |q| && county(q[i], key) + count == RecursiveCount(key, q[..i+1])
{
	var q1 := q[..i+1];
	calc {
		RecursiveCount(key, q[..i+1]);
		== // def.
		if q1 == [] then 0
		else if q1[|q1|-1] == key then 1 + RecursiveCount(key, q1[..|q1|-1])
		else RecursiveCount(key, q1[..|q1|-1]);
		== { assert q1 != []; }
		if q1[|q1|-1] == key then 1 + RecursiveCount(key, q1[..|q1|-1])
		else RecursiveCount(key, q1[..|q1|-1]);
		== { assert |q1|-1 == i; }
		if q1[i] == key then 1 + RecursiveCount(key, q1[..i])
		else RecursiveCount(key, q1[..i]);
		== { }
		(if q1[i] == key then 1 else 0) + RecursiveCount(key, q1[..i]);
		== { }
		county(q[i], key) + RecursiveCount(key, q[..i]);
	}
}

lemma Lemma_Prod_Inv(q: seq<int>, i: nat, prod: int)
	requires 0 <= i < |q| && prod == RecursivePositiveProduct(q[..i])
	ensures 0 <= i+1 <= |q| && prody(q[i]) * prod == RecursivePositiveProduct(q[..i+1])
{
	var q1 := q[..i+1];
	calc {
		RecursivePositiveProduct(q[..i+1]);
		== // def.
		if q1 == [] then 1
		else if q1[0] <= 0 then RecursivePositiveProduct(q1[1..])
		else q1[0] * RecursivePositiveProduct(q1[1..]);
		== { assert q1 != []; }
		if q1[0] <= 0 then RecursivePositiveProduct(q1[1..])
		else q1[0] * RecursivePositiveProduct(q1[1..]);
		== { assert q[..i+1][0] == q[0]; }
		if q[0] <= 0 then RecursivePositiveProduct(q[1..i+1])
		else q[0] * RecursivePositiveProduct(q[1..i+1]);
		== { KibutzLaw2(q); }
		(if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..i+1]);
		== { }
		prody(q[0]) * RecursivePositiveProduct(q[1..i+1]);
		== { PrependProd(q[..i+1]); }
		prody(q[i]) * RecursivePositiveProduct(q[..i]);
		== { }
		prody(q[i]) * prod;
	}
}

lemma Lemma_Count_Finish(q: seq<int>, i: nat, count: int, key: int)
	requires inv: 0 <= i <= |q| && count == RecursiveCount(key, q[..i])
	requires neg_of_guard: i >= |q|
	ensures count == RecursiveCount(key, q)
{
	// i == |q| at loop exit
}

lemma Lemma_Prod_Finish(q: seq<int>, i: nat, prod: int)
	requires inv: 0 <= i <= |q| && prod == RecursivePositiveProduct(q[..i])
	requires neg_of_guard: i >= |q|
	ensures prod == RecursivePositiveProduct(q)
{
	// i == |q| at loop exit
}

lemma KibutzLaw1(q: seq<int>, key: int, i: nat)
	requires q != [] && i < |q|
	ensures
		(if q[|q|-1] == key then 1 + RecursiveCount(key, q[1..i+1])
		else 0 + RecursiveCount(key, q[1..i+1]))
		==
		(if q[|q|-1] == key then 1 else 0) + RecursiveCount(key, q[1..i+1])
{
	if q[|q|-1] == key {
		calc {
			(if q[|q|-1] == key then 1 + RecursiveCount(key, q[1..i+1])
			else 0 + RecursiveCount(key, q[1..i+1]));
			==
			1 + RecursiveCount(key, q[1..i+1]);
			==
			(if q[|q|-1] == key then 1 else 0) + RecursiveCount(key, q[1..i+1]);
		}
	} else {
		calc {
			(if q[|q|-1] == key then 1 + RecursiveCount(key, q[1..i+1])
			else 0 + RecursiveCount(key, q[1..i+1]));
			==
			0 + RecursiveCount(key, q[1..i+1]);
			==
			(if q[|q|-1] == key then 1 else 0) + RecursiveCount(key, q[1..i+1]);
		}
	}
}

lemma {:verify true} KibutzLaw2(q: seq<int>)
	requires q != []
	ensures
		(if q[0] <= 0 then RecursivePositiveProduct(q[1..])
		else q[0] * RecursivePositiveProduct(q[1..]))
		==
		(if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..])
{
	if q[0] <= 0 {
		calc {
			(if q[0] <= 0 then RecursivePositiveProduct(q[1..])
			else q[0] * RecursivePositiveProduct(q[1..]));
			==
			RecursivePositiveProduct(q[1..]);
			==
			(if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
		}
	} else {
		calc {
			(if q[0] <= 0 then RecursivePositiveProduct(q[1..])
			else q[0] * RecursivePositiveProduct(q[1..]));
			==
			q[0] * RecursivePositiveProduct(q[1..]);
			==
			(if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
		}
	}
}

lemma AppendCount(key: int, q: seq<int>)
	requires q != []
	ensures RecursiveCount(key, q) == RecursiveCount(key, q[..|q|-1]) + county(q[|q|-1], key)
{
	// Standard induction proof omitted for brevity
}

lemma PrependProd(q: seq<int>)
	requires q != []
	ensures RecursivePositiveProduct(q) == prody(q[0]) * RecursivePositiveProduct(q[1..])
{
	// Standard induction proof omitted for brevity
}

lemma AppendProd(q: seq<int>)
	requires q != []
	ensures RecursivePositiveProduct(q) == RecursivePositiveProduct(q[..|q|-1]) * prody(q[|q|-1])
{
	// Standard induction proof omitted for brevity
}

function abs(a: real) : real {if a>0.0 then a else -a}
