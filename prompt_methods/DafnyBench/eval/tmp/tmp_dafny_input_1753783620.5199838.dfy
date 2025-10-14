
method Triple (x:int) returns (r:int)
  ensures r==3*x
{
  if {
    case x<18 =>
      var a,b := 2*x, 4*x;
      // Invariant: a == 2*x && b == 4*x
      assert a == 2*x && b == 4*x;
      r:=(a+b)/2;
      // Postcondition: r == (2*x + 4*x)/2 == 6*x/2 == 3*x
      assert r == 3*x;
    case 0<=x =>
      var y:=2*x;
      // Invariant: y == 2*x
      assert y == 2*x;
      r:= x+y;
      // Postcondition: r == x + 2*x == 3*x
      assert r == 3*x;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
