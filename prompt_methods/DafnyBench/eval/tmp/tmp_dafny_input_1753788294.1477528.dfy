// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function M1(f:map<int, bool>, i:int):bool

function M2(f:map<int, bool>, i:int):bool
{
    // M2 returns M1 applied to the map comprehension and i
    // The map comprehension is equivalent to f itself
    M1(map j | j in f :: f[j], i)
}

lemma L(f:map<int, bool>, i:int)
    requires i in f;
    requires M2(f, i);
    requires forall j:int, f:map<int, bool> :: M1(f, j) == (j in f && f[j]);
{
    // By the third precondition, M1(f, i) == (i in f && f[i])
    // By the first precondition, i in f
    // By the second precondition, M2(f, i) == M1(map j | j in f :: f[j], i)
    // The map comprehension is equivalent to f, so M2(f, i) == M1(f, i)
    assert M1(f, i) == (i in f && f[i]);
    assert i in f;
    assert M2(f, i) == M1(f, i);
    assert M1(f, i);
}
function abs(a: real) : real {if a>0.0 then a else -a}
