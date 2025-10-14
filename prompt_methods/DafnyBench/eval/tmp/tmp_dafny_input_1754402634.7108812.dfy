
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1

{
	var i: int := 0;
	// Invariant: All indices before i do not contain 'e'
	while i < a.Length
		invariant 0 <= i <= a.Length
		invariant forall j :: 0 <= j < i ==> a[j] != 'e'
	{
		if (a[i] == 'e') {
			assert 0 <= i < a.Length;
			assert a[i] == 'e';
			assert forall j :: 0 <= j < i ==> a[j] != 'e';
			return i;
		}
		i := i + 1;
	}
	assert forall j :: 0 <= j < a.Length ==> a[j] != 'e';
	return -1;
}

method Main() {
	var a: array<char> := new char[]['c','h','e','e','s','e'];
	var res := firstE(a);
	
	a := new char[]['e'];
	res := firstE(a);
	
	a := new char[][];
	res := firstE(a);
}

function abs(a: real) : real {if a>0.0 then a else -a}
