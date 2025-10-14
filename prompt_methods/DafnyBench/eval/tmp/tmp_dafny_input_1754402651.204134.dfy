predicate acheck(a: array<int>, n: int)
reads a
requires n >= 1
{
	a.Length % 2 == 0 && 
	forall i :: 0 <= i < a.Length ==> 
		if i % n == 0 then a[i] == 0 else a[i] != 0
}

method Main()
{
	var arr: array<int> := new int[][0,42,0,42];
	// arr.Length == 4, arr[0] == 0, arr[2] == 0, arr[1] == 42, arr[3] == 42
	assert arr.Length % 2 == 0;
	assert arr[0] == 0 && arr[2] == 0;
	assert arr[1] != 0 && arr[3] != 0;
	assert forall i :: 0 <= i < arr.Length ==> (if i % 2 == 0 then arr[i] == 0 else arr[i] != 0);
	var res := acheck(arr, 2);
	assert res;

	arr := new int[][];
	// arr.Length == 0
	assert arr.Length % 2 == 0;
	// vacuously true: forall i :: 0 <= i < arr.Length ==> ...
	assert forall i :: 0 <= i < arr.Length ==> (if i % 2 == 0 then arr[i] == 0 else arr[i] != 0);
	res := acheck(arr, 2);
	assert res;

	arr := new int[][0,4,2,0];
	// arr.Length == 4, arr[0] == 0, arr[1] == 4, arr[2] == 2, arr[3] == 0
	assert arr.Length % 2 == 0;
	assert arr[0] == 0 && arr[2] == 2;
	assert arr[1] == 4 && arr[3] == 0;
	// Now check the property for acheck(arr, 2):
	// i=0: 0%2==0 => arr[0]==0 (true)
	// i=1: 1%2==1 => arr[1]!=0 (true)
	// i=2: 2%2==0 => arr[2]==0 (false! arr[2]==2)
	// i=3: 3%2==1 => arr[3]!=0 (false! arr[3]==0)
	assert !(forall i :: 0 <= i < arr.Length ==> (if i % 2 == 0 then arr[i] == 0 else arr[i] != 0));
	res := acheck(arr, 2);
	assert !res;
}
function abs(a: real) : real {if a>0.0 then a else -a}
