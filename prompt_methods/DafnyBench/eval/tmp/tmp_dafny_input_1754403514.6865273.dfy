// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function M1(f:map<int, bool>, i:int):bool

function M2(f:map<int, bool>, i:int):bool
{
    M1(map j | j in f :: f[j], i)
}

lemma L(f:map<int, bool>, i:int)
    requires i in f;
    requires M2(f, i);
    requires forall j:int, f:map<int, bool> :: M1(f, j) == (j in f && f[j]);
{
    // The strongest assertions based on the preconditions and the code
    assert map j | j in f :: f[j] == f;
    assert M2(f, i) == M1(f, i);
    assert M1(f, i) == (i in f && f[i]);
    assert i in f;
    assert f[i];
}

function abs(a: real) : real {if a>0.0 then a else -a}
