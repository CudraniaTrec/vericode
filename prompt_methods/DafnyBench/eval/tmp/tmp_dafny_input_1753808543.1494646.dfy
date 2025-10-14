module Utils {
  class Assertions<T> {
    static method {:extern} assertEquals(expected : T, actual : T)
    requires expected == actual
    ensures expected == actual
    {
      assert expected == actual;
    }

    static method {:extern} expectEquals(expected : T, actual : T)
    ensures expected == actual
    {
      assert expected == actual;
    }

    static method {:extern} assertTrue(condition : bool)
    requires condition
    ensures condition
    {
      assert condition;
    }

    static method {:extern} expectTrue(condition : bool)
    ensures condition
    {
      assert condition;
    }
    
    static method {:extern} assertFalse(condition : bool)
    requires !condition
    ensures !condition
    {
      assert !condition;
    }

    static method {:extern} expectFalse(condition : bool)
    ensures !condition
    {
      assert !condition;
    }
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
