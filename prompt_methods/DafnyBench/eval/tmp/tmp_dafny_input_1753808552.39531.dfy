
module Utils {

    export 
        reveals Assertions
        provides Assertions.assertEquals

    class Assertions {
        static method {:axiom} assertEquals<T>(left : T, right : T)
        requires left == right
        ensures left == right
        {
            // Strongest annotation: nothing to prove, as it's an axiom and requires left == right
            assert left == right;
        }

        static method {:axiom} assertTrue(value : bool)
        requires value
        ensures value
        {
            assert value;
        }

        static method {:axiom} assertFalse(value : bool)
        requires !value
        ensures !value
        {
            assert !value;
        }
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
