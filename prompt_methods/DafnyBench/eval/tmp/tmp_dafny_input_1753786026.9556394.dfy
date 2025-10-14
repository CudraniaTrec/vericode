method max(x:array<nat>) returns (y:nat) 
requires x.Length > 0
ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
ensures y in x[..]
{
    y := x[0];
    var i := 1;
    while(i < x.Length)
        invariant 1 <= i <= x.Length
        invariant y in x[..i]
        invariant forall j :: 0 <= j < i ==> y >= x[j]
    {
        if(y <= x[i]){
            y := x[i];
        }
        i := i + 1;
    }
    assert y in x[..];
    assert forall j :: 0 <= j < x.Length ==> y >= x[j];
}

method Main()
{
    var a := new nat [6][5, 1, 3, 6, 12, 3];
    var c := max(a);
    // print c;
}
function abs(a: real) : real {if a>0.0 then a else -a}
