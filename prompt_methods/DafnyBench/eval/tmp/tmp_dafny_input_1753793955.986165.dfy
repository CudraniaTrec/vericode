
function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{
    a[i] + if i == 0 then 0 else sum(a, i - 1)
}

method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b
    // when you change a  , that's not the same object than b . 
    //requires b.Length > 0 
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
{
    b[0] := a[0]; // Initialise le premier élément de b
    var i := 1;

    // Invariant: For all j in 0..i-1, b[j] == sum(a, j)
    // Invariant: 1 <= i <= a.Length
    // Invariant: b[0] == a[0]
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant b[0] == a[0]
        invariant forall j :: 0 <= j < i ==> b[j] == sum(a, j)
    {
        // assert b[i-1] == sum(a, i-1);
        b[i] := b[i - 1] + a[i]; // Calcule la somme cumulée pour chaque élément
        // assert b[i] == sum(a, i);
        i := i + 1;
    }
    // assert forall j :: 0 <= j < a.Length ==> b[j] == sum(a, j);
}

function abs(a: real) : real {if a>0.0 then a else -a}
