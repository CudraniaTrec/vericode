module Utils {

    export 
        reveals Assertions
        provides Assertions.assertEquals

    class Assertions {
        static method {:axiom} assertEquals<T>(left : T, right : T)
        requires left == right
        ensures left == right
        {
            // Strongest assertion: left == right
            assert left == right;
        }

        /*
public static void assertEquals<T>(T a, T b) {
    Xunit.Assert.Equal(a, b);
}
        */

        /*
static public <T> void assertEquals(dafny.TypeDescriptor<T> typeDescriptor, T left, T right) {
    org.junit.jupiter.api.Assertions.assertEquals(left, right);
}
        */

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
