
predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
	var i: nat := 0;
	index := a.Length;
	if a.Length < 3 {
		return a.Length;
	}
	while i < a.Length - 2
		invariant 0 <= i <= a.Length - 2
		invariant forall j :: 0 <= j < i ==> a[j] != a[j + 1] || a[j] != a[j + 2]
		invariant (forall j :: 0 <= j < i ==> !(a[j] == a[j + 1] == a[j + 2]))
		invariant index == a.Length
	{
		if a[i] == a[i + 1] == a[i + 2] {
			assert 0 <= i < a.Length - 2;
			assert a[i] == a[i + 1] && a[i] == a[i + 2];
			return i;
		}
		i := i + 1;
	}
	assert i == a.Length - 2 || i == a.Length - 1 || i == a.Length;
	assert forall j :: 0 <= j < a.Length - 2 ==> !(a[j] == a[j + 1] == a[j + 2]);
}

method TesterGetTriple()
{
    var a: array<int> := new int[1][42];
    var b := GetTriple(a);

    a := new int[2][42,42];
    b := GetTriple(a);

    a := new int[3][42,42,0];
    b := GetTriple(a);

    a := new int[4][42,42,0,42];
    b := GetTriple(a);

    a := new int[3][42,42,42];
    b := GetTriple(a);

    a := new int[4][0,42,42,42];
    b := GetTriple(a);

    a := new int[6][0,0,42,42,42,0];
    b := GetTriple(a);
}

function abs(a: real) : real {if a>0.0 then a else -a}
