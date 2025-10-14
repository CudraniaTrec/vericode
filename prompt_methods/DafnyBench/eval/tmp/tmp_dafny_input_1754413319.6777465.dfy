
// RUN: /nologo /rlimit:10000000 /noNLarith

abstract module Interface {
    function addSome(n: nat): nat
        ensures addSome(n) > n
}

abstract module Mod {
    import A : Interface
    method m() {
        print "Test\n";
        // No loops or complex code, nothing to annotate here.
        assert true; // Strongest assertion possible in this context.
    }
}

module Implementation refines Interface {
    function addSome(n: nat): nat
        ensures addSome(n) == n + 1
    {
        assert n >= 0; // strongest precondition from nat
        assert n + 1 > n; // strongest assertion for ensures in Interface
        n + 1
    }
}

module Mod2 refines Mod {
  import A = Implementation
}

method Main() {
    Mod2.m();
}

function abs(a: real) : real {if a>0.0 then a else -a}
