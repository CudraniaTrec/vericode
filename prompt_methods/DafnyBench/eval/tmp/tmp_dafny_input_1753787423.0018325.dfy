
method MaxArray(a: array<int>) returns (max:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
ensures exists i :: 0 <= i < a.Length && a[i] == max
{
	var i: nat := 1;
	max := a[0];
	// Invariant: max is the maximum of a[0..i)
	while i < a.Length
		invariant 1 <= i <= a.Length
		invariant forall j :: 0 <= j < i ==> a[j] <= max
		invariant exists j :: 0 <= j < i && a[j] == max
	{
		if (a[i] > max) {
			max := a[i];
		}
		i := i + 1;
	}
	// At this point, i == a.Length
	// assert forall j :: 0 <= j < a.Length ==> a[j] <= max;
	// assert exists j :: 0 <= j < a.Length && a[j] == max;
}

method Main() {
	var arr : array<int> := new int[][-11,2,42,-4];
	var res := MaxArray(arr);
}

function abs(a: real) : real {if a>0.0 then a else -a}
