
// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function M1(f:map<int, bool>, i:int):bool
    ensures M1(f, i) == (i in f && f[i]);

function M2(f:map<int, bool>, i:int):bool
{
    // Strongest annotation: for all j in f, f[j] is the value at j, so this map comprehension is just f itself.
    // So M1(map j | j in f :: f[j], i) == M1(f, i)
    M1(map j | j in f :: f[j], i)
}

lemma L(f:map<int, bool>, i:int)
    requires i in f;
    requires M2(f, i);
    requires forall j:int, f:map<int, bool> :: M1(f, j) == (j in f && f[j]);
    ensures M1(f, i);
{
    // Strongest possible annotation: by the third precondition, M1(f, i) == (i in f && f[i])
    // By first precondition, i in f
    // By second precondition, M2(f, i) holds, i.e., M1(f, i) holds
    assert M1(f, i) == (i in f && f[i]);
    assert i in f;
    assert M2(f, i);
    assert M1(f, i);
}

function abs(a: real) : real {if a>0.0 then a else -a}
