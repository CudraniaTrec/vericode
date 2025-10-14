method Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
{
  // No loop or complex logic; strongest annotation is to assert the postcondition
  result := a * b;
  assert result == a * b;
}
function abs(a: real) : real {if a>0.0 then a else -a}
