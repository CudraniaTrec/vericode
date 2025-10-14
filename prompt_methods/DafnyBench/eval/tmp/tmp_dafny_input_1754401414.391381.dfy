// Given an array of positive and negative integers,
//  it returns an array of the absolute value of all the integers. [-4,1,5,-2,-5]->[4,1,5,2,5]

function AbsVal(x:int):nat
{
    if x < 0 then -x else x
}

method absx(x:array<int>) returns (y:array<int>) 
ensures y.Length == x.Length
ensures forall i :: 0 <= i < y.Length ==>  y[i] == AbsVal(x[i])
{   
  y := new int[x.Length];
  var j := 0;
  while (j < y.Length)
    invariant 0 <= j <= y.Length
    invariant y.Length == x.Length
    invariant forall i :: 0 <= i < j ==> y[i] == AbsVal(x[i])
  {
      if x[j] < 0 {
          y[j] := -x[j];
          assert y[j] == AbsVal(x[j]);
      } else {
          y[j] := x[j];
          assert y[j] == AbsVal(x[j]);
      }
      j := j + 1;
  }
}

method Main() {
    var d := new int [5];
    var c := new int [5];
    d[0], d[1], d[2], d[3], d[4] := -4, 1, 5, -2 , -5;
    //c[0], c[1], c[2], c[3], c[4] := 4, 1, 5, 2 , 5;
    c := absx(d);
    //assert forall x :: 0<=x<c.Length ==> c[x] >= 0;
    print c[..];
}

function abs(a: real) : real {if a>0.0 then a else -a}
