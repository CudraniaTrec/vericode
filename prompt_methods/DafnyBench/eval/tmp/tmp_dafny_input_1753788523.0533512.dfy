// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function{:opaque} f(x:int):int { x }

lemma L()
    ensures forall x:int :: f(x) == x
{
    reveal f();
}
function abs(a: real) : real {if a>0.0 then a else -a}
