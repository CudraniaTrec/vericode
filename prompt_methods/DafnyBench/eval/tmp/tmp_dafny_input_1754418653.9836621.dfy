// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
{
	// if length = 1, return first element
	if a.Length == 1
	{ seclar := a[0]; }
	else 
	{
		var l, s, i: int := 0, 0, 2;

		// set initial largest and second largest
		if a[1] > a[0]
		{ l := a[1]; s := a[0]; }
		else 
		{ l := a[0]; s := a[1]; }

		// Loop invariants:
		// 1. 2 <= i <= a.Length
		// 2. l is the largest value among a[0..i-1]
		// 3. s is the largest value among a[0..i-1] that is less than l, or s == l if all values so far are equal
		// 4. forall j :: 0 <= j < i ==> a[j] <= l
		// 5. forall j :: 0 <= j < i && a[j] != l ==> a[j] <= s
		// 6. s <= l
		while i < a.Length
			invariant 2 <= i <= a.Length
			invariant forall j :: 0 <= j < i ==> a[j] <= l
			invariant forall j :: 0 <= j < i && a[j] != l ==> a[j] <= s
			invariant s <= l
		{
			if a[i] > l
			{ s := l; l := a[i]; }
			else if a[i] > s && a[i] < l
			{ s := a[i]; }
			else if l == s && a[i] < s
			{ s := a[i]; }
			i := i + 1;
		}
		seclar := s;
	}
}

method Main()
{
	var a: array<int> := new int[][1];
	var x:int := SecondLargest(a);
//	assert x == 1;

	var b: array<int> := new int[][9,1];
	x := SecondLargest(b);
//	assert x == 1;
	
	var c: array<int> := new int[][1,9];
	x := SecondLargest(c);
//	assert x == 1;

	var d: array<int> := new int[][2,42,-4,123,42];
	x := SecondLargest(d);
//	assert x == 42;

	var e: array<int> := new int[][1,9,8];
	x := SecondLargest(e);
//	assert x == 8;
}

function abs(a: real) : real {if a>0.0 then a else -a}
