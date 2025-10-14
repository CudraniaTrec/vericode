
// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
module ModOpaque {
    function {:opaque} Hidden(x:int) : (int, int)
    {
        (5, 7)
    }

    function Visible(x:int) : (int, int)
    {
        Hidden(x)
    }

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }
}

module ModVisible {
    function Hidden(x:int) : (int, int)
    {
        (5, 7)
    }

    function Visible(x:int) : (int, int)
    {
        Hidden(x)
    }

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }
}

module ModFuel {
    function {:fuel 0,0} Hidden(x:int) : (int, int)
    {
        (5, 7)
    }

    function Visible(x:int) : (int, int)
    {
        Hidden(x)
    }

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
        assert Visible(x) == Hidden(x);
        assert Hidden(x) == (5, 7);
        assert y == 5;
        assert z == 7;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
