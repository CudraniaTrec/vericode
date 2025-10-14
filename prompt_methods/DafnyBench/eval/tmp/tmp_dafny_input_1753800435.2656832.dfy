
// RUN: /nologo /rlimit:10000000 /noNLarith

abstract module Interface {
    function addSome(n: nat): nat
        ensures addSome(n) > n
}

abstract module Mod {
    import A : Interface
    method m() {
        // Strongest annotation: nothing to prove here, but let's assert the interface property
        var x := A.addSome(5);
        assert x > 5;
        print "Test\n";
    }
}

module Implementation refines Interface {
    function addSome(n: nat): nat
        ensures addSome(n) == n + 1
    {
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
