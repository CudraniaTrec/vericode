
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
		var l, s, i: int := 0, 0, 0;

		// set initial largest and second largest
		if a[1] > a[0]
		{ l := a[1]; s := a[0]; }
		else 
		{ l := a[0]; s := a[1]; }

		i := 2;
		// At this point, l and s are the largest and second largest among a[0] and a[1]
		// Loop invariant: 
		//   0 <= i <= a.Length
		//   l is the largest among a[0..i-1]
		//   s is the second largest among a[0..i-1], or equal to l if all values so far are equal
		//   forall j :: 0 <= j < i ==> a[j] <= l
		//   forall j :: 0 <= j < i && a[j] != l ==> a[j] <= s
		//   s <= l
		//   exists j :: 0 <= j < i && a[j] == l
		//   forall j :: 0 <= j < i && a[j] != l ==> exists k :: 0 <= k < i && a[k] == s && a[k] != l
		while i < a.Length
			invariant 2 <= i <= a.Length
			invariant forall j :: 0 <= j < i ==> a[j] <= l
			invariant forall j :: 0 <= j < i && a[j] != l ==> a[j] <= s
			invariant s <= l
			invariant exists j :: 0 <= j < i && a[j] == l
			invariant (forall j :: 0 <= j < i && a[j] != l ==> exists k :: 0 <= k < i && a[k] == s && a[k] != l)
		{
			if a[i] > l						// check if curr is greater then largest and set l and s
			{ s := l; l := a[i]; }
			if a[i] > s && a[i] < l			// check if curr is greater than s and set s
			{ s := a[i]; }
			if s == l && s > a[i]			// check s is not the same as l
			{ s := a[i]; }
			i := i+1;
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
