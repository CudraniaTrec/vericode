method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
ensures c.Length == a.Length + b.Length
ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
{
	c := new int[a.Length + b.Length];

	var i := 0;
	while i < a.Length
		invariant 0 <= i <= a.Length
		invariant forall j :: 0 <= j < i ==> c[j] == a[j]
		invariant forall j :: a.Length <= j < c.Length ==> c[j] == 0
	{
		c[i] := a[i];
		i := i + 1;
	}

	while i < b.Length + a.Length
		invariant a.Length <= i <= a.Length + b.Length
		invariant forall j :: 0 <= j < a.Length ==> c[j] == a[j]
		invariant forall j :: a.Length <= j < i ==> c[j] == b[j - a.Length]
		invariant forall j :: i <= j < c.Length ==> c[j] == 0
	{
		c[i] := b[i - a.Length];
		i := i + 1;
	}
}
function abs(a: real) : real {if a>0.0 then a else -a}
