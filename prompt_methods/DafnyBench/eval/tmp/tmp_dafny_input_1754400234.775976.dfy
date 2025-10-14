
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
ensures |pop(s)| == |s| - 1
ensures pop(s) == s[..|s|-1]
{
   s[..|s|-1] 
}

method testStack() returns (r: intStack)
ensures r == [20, 30, 15, 40, 60, 100, 80]
{
  var s: intStack := [20, 30, 15, 40, 60, 100, 80];

  // Invariant: s is a sequence of 7 elements with the given values
  assert |s| == 7;
  assert s[0] == 20 && s[1] == 30 && s[2] == 15 && s[3] == 40 && s[4] == 60 && s[5] == 100 && s[6] == 80;

  r:= s;
}

method Main()
{
    var t:=testStack();
    print "Stack tested\nStack is ", t, "\n";
}

function abs(a: real) : real {if a>0.0 then a else -a}
