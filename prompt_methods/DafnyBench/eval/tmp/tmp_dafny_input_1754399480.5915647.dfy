method M(x: int) returns (seven: int)
  ensures seven==7
{
  // seven is assigned 7, so postcondition will hold
  seven := 7;
  assert seven == 7;
}
function abs(a: real) : real {if a>0.0 then a else -a}
