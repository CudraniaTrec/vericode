
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
  ensures |push(s, x)| == |s| + 1
  ensures push(s, x)[..|s|] == s
  ensures push(s, x)[|s|] == x
{
    s + [x]
}

function pop(s: intStack): intStack
requires !isEmpty(s)
ensures |pop(s)| == |s| - 1
ensures pop(s) == s[..|s|-1]
{
   s[..|s|-1] 
}

method testStack() returns (r: intStack)
  ensures r == [20, 30, 15, 40, 60, 100, 80]
{
  var s: intStack := [20, 30, 15, 40, 60, 100, 80];

  // Check initial stack is not empty
  assert !isEmpty(s);

  // Check push correctness
  var s2 := push(s, 42);
  assert |s2| == |s| + 1;
  assert s2[..|s|] == s;
  assert s2[|s|] == 42;

  // Check pop correctness
  var s3 := pop(s2);
  assert s3 == s2[..|s2|-1];
  assert s3 == s;

  r:= s;
}

method Main()
{
    var t:=testStack();
    print "Stack tested\nStack is ", t, "\n";
}

function abs(a: real) : real {if a>0.0 then a else -a}
