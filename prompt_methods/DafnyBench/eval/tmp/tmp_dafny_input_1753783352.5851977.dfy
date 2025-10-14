method ComputeIsEven(x:int) returns (is_even:bool)
  ensures (x % 2 == 0)==is_even
{
  is_even:=false;
  assert is_even == false;
  if x%2==0{
    is_even:=true;
    assert is_even == true;
  }
  assert (x % 2 == 0)==is_even;
}
function abs(a: real) : real {if a>0.0 then a else -a}
