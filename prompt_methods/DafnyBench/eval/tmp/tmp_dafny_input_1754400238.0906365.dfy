/* 
  Dafny Tutorial 2: Sequences and Stacks, Predicates and Assertions

  In this tutorial we introduce a simple stack model using the functional 
  style of programming.
  
*/
type intStack = seq<int>

function isEmpty(s: intStack): bool
{
    |s| == 0
}

function push(s: intStack, x: int): intStack
{
    s + [x]
}

function pop(s: intStack): intStack
requires !isEmpty(s)
{
   s[..|s|-1] 
}

method testStack() returns (r: intStack)
{
  var s: intStack := [20, 30, 15, 40, 60, 100, 80];

  // Strongest possible assertions about s
  assert |s| == 7;
  assert s[0] == 20;
  assert s[1] == 30;
  assert s[2] == 15;
  assert s[3] == 40;
  assert s[4] == 60;
  assert s[5] == 100;
  assert s[6] == 80;
  assert !isEmpty(s);
  assert pop(s) == [20, 30, 15, 40, 60, 100];

  r:= s;
}

method Main()
{
    var t:=testStack();
    print "Stack tested\nStack is ", t, "\n";
}

function abs(a: real) : real {if a>0.0 then a else -a}
