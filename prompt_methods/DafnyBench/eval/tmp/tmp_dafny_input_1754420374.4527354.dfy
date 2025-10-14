
function SomaAte(a:array<nat>, i:nat):nat
  requires 0 <= i <= a.Length
  reads a
{
    if i == 0
    then 0
    else a[i-1] + SomaAte(a,i-1)
}

method Somatorio(a:array<nat>) returns (s:nat)
  ensures s == SomaAte(a,a.Length)
{
    var i := 0;
    s := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant s == SomaAte(a, i)
    {
        s := s + a[i];
        i := i + 1;
    }
    assert i == a.Length;
    assert s == SomaAte(a, a.Length);
}

function abs(a: real) : real {if a>0.0 then a else -a}
