module Utils {

    export 
        reveals Assertions
        provides Assertions.assertEquals

    class Assertions {
        static method {:axiom} assertEquals<T>(left : T, right : T)
        requires left == right
        {
            assert left == right;
        }

        static method {:axiom} assertTrue(value : bool)
        requires value
        {
            assert value;
        }

        static method {:axiom} assertFalse(value : bool)
        requires !value
        {
            assert !value;
        }
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
