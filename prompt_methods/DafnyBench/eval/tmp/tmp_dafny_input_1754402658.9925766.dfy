
method Deli(a: array<char>, i: nat)
modifies a
requires a.Length > 0
requires 0 <= i < a.Length
ensures forall j :: 0 <= j < i ==> a[j] == old(a[j])
ensures forall j :: i <= j < a.Length - 1 ==> a[j] == old(a[j + 1])
ensures a[a.Length - 1] == '.'
{
	var c := i;
	while c < a.Length - 1
		invariant i <= c <= a.Length - 1
		invariant forall j :: 0 <= j < i ==> a[j] == old(a[j])
		invariant forall j :: i <= j < c ==> a[j] == old(a[j + 1])
		invariant forall j :: c < j < a.Length ==> a[j] == old(a[j])
		decreases a.Length - 1 - c
	// unchanged first half
	{
		a[c] := a[c + 1];
		c := c + 1;
	}
	a[c] := '.';
}

method DeliChecker()
{
   var z := new char[]['b','r','o','o','m'];
   Deli(z, 1);
   Deli(z, 3);
   Deli(z, 4);
   Deli(z, 3);
   Deli(z, 0);
   Deli(z, 0);
   Deli(z, 0);

   z := new char[]['x'];
   Deli(z, 0);
}

function abs(a: real) : real {if a>0.0 then a else -a}
