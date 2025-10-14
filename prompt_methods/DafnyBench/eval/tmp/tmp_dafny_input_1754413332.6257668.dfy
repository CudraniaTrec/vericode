// RUN: /nologo /rlimit:10000000 /noNLarith

abstract module Interface {
    function addSome(n: nat): nat
        ensures addSome(n) > n
}

abstract module Mod {
    import A : Interface
    method m() {
        print "Test\n";
        assert true;
    }
}

module Implementation refines Interface {
    function addSome(n: nat): nat
        ensures addSome(n) > n
    {
        assert n >= 0;
        assert n + 1 > n;
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
