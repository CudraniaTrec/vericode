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
        // Can't reason about Hidden(x) being (5,7) due to opacity
        assert (y, z) == Visible(x);
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        // Can't reason about Hidden(x) being (5,7) due to opacity
        assert y == Visible(x).0;
        assert z == Visible(x).1;
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        // Can't reason about Hidden(x) being (5,7) due to opacity
        assert y == Visible(x).0;
        assert z == Visible(x).1;
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
        // Can't assert Visible(x) == (5, 7) without further context
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert y == Visible(x).0;
        assert z == Visible(x).1;
        // Can't assert Visible(x) == (5, 7) without further context
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert y == Visible(x).0;
        assert z == Visible(x).1;
        // Can't assert Visible(x) == (5, 7) without further context
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
        // Can't assert Visible(x) == (5, 7) without further context
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert y == Visible(x).0;
        assert z == Visible(x).1;
        // Can't assert Visible(x) == (5, 7) without further context
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert y == Visible(x).0;
        assert z == Visible(x).1;
        // Can't assert Visible(x) == (5, 7) without further context
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
