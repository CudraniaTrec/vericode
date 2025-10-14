method HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
  assert (a < 0 && b > 0) || (a > 0 && b < 0) <==> ((a < 0 && b > 0) || (a > 0 && b < 0));
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
  assert result <==> ((a < 0 && b > 0) || (a > 0 && b < 0));
}
function abs(a: real) : real {if a>0.0 then a else -a}
