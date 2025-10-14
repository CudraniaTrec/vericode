// line contém uma string de tamanho l
// remover p caracteres a partir da posição at
method Delete(line:array<char>, l:nat, at:nat, p:nat)
  requires l <= line.Length
  requires at+p <= l
  modifies line
  ensures line[..at] == old(line[..at])
  ensures line[at..l-p] == old(line[at+p..l])
{
    var i:nat := 0;
    while i < l-(at+p)
        invariant 0 <= i <= l-(at+p)
        invariant line[..at] == old(line[..at])
        invariant forall j :: 0 <= j < i ==> line[at+j] == old(line[at+p+j])
        invariant forall j :: i <= j < l-(at+p) ==> line[at+j] == old(line[at+j])
        invariant line[l-(at+p)..l] == old(line[l-(at+p)..l])
    { 
        line[at+i] := line[at+p+i];
        i := i+1;
    }
    // assert line[..at] == old(line[..at]);
    // assert forall j :: 0 <= j < l-(at+p) ==> line[at+j] == old(line[at+p+j]);
    // assert line[l-(at+p)..l] == old(line[l-(at+p)..l]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
