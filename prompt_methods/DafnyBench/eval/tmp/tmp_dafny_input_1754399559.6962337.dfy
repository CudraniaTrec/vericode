method Triple (x:int) returns (r:int)
  ensures r==3*x
{
  if x==0 {
    r:=0;
    assert r == 3*x;
  }
  else{
    var y:=2*x;
    assert y == 2*x;
    r:= x+y;
    assert r == x + 2*x;
    assert r == 3*x;
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
