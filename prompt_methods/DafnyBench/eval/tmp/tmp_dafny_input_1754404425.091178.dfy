
method MaxSum(x:int, y:int) returns (s:int, m:int)
    ensures s == x+y
    ensures (m == x || m == y) && x <= m && y <= m
{
    // s is the sum of x and y
    s := x+y;
    // At this point, s == x + y
    assert s == x + y;

    if x > y{
      // x is greater, so m should be x
      m := x;
      assert m == x;
      assert x <= m && y <= m;
    } else if y > x{
      // y is greater, so m should be y
      m := y;
      assert m == y;
      assert x <= m && y <= m;
    } else {
      // x == y, so m can be either x or y
      assert x == y;
      m := x;
      assert m == x && m == y;
      assert x <= m && y <= m;
    }
    assert (m == x || m == y) && x <= m && y <= m;
}

method Main() 
{
  var m, n := 4,5;
  var a,b := MaxSum(m,n);
  print "Search return a is ", a,",,,,, b is ", b, "\n";
}

function abs(a: real) : real {if a>0.0 then a else -a}
