
method addArrays(a : array<int>, b : array<int>) returns (c : array<int>) 
requires a.Length == b.Length
ensures b.Length == c.Length
ensures forall i:int :: 0 <= i <c.Length ==> c[i] == a[i] + b[i]

{
     c := new int[a.Length];
     var j := 0;
     while (j < a.Length) 
        invariant 0 <= j <= a.Length
        invariant c.Length == a.Length
        invariant forall i:int :: 0 <= i < j ==> c[i] == a[i] + b[i]
     {    
          c[j] := a[j] + b[j];
          j := j + 1;      
    }
    assert c.Length == b.Length;
    assert forall i:int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i];
}

function abs(a: real) : real {if a>0.0 then a else -a}
