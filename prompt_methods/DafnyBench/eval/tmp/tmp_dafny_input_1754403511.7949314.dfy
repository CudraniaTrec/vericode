
// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function M1(f:map<int, bool>, i:int):bool
    ensures M1(f, i) == (i in f && f[i]);

function M2(f:map<int, bool>, i:int):bool
{
    M1(map j | j in f :: f[j], i)
}

lemma L(f:map<int, bool>, i:int)
    requires i in f;
    requires M2(f, i);
    requires forall j:int, f:map<int, bool> :: M1(f, j) == (j in f && f[j]);
    ensures f[i];
{
    // Strongest annotation: assert M2(f, i) == (i in f && f[i]);
    assert M2(f, i) == (i in f && f[i]);
    assert i in f;
    assert M2(f, i);
    assert forall j:int, f:map<int, bool> :: M1(f, j) == (j in f && f[j]);
    assert M1(map j | j in f :: f[j], i) == (i in (map j | j in f :: f[j]) && (map j | j in f :: f[j])[i]);
    assert (map j | j in f :: f[j]) == f;
    assert (map j | j in f :: f[j])[i] == f[i];
    assert i in (map j | j in f :: f[j]);
    assert (map j | j in f :: f[j])[i] == f[i];
    assert f[i];
}

function abs(a: real) : real {if a>0.0 then a else -a}
