
/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2021
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example adapted from material by Graeme Smith
*/

/////////////////////
// Modifying arrays 
/////////////////////


method SetEndPoints(a: array<int>, left: int, right: int)
  requires a.Length != 0 
  modifies a 
{  
  // Strongest annotation: endpoints set, rest unchanged
  assert a.Length > 0;
  var oldA := a[..];
  a[0] := left; 
  a[a.Length - 1] := right;  
  assert a[0] == left;
  assert a[a.Length - 1] == right;
  if a.Length > 2 {
    assert forall i :: 1 <= i < a.Length - 1 ==> a[i] == oldA[i];
  }
}


method Aliases(a: array<int>, b: array<int>) 
	requires a.Length >= b.Length > 100  
	modifies a 
{ 
  // Strongest annotation: a, c, b may alias; only a is modified
  assert a.Length >= b.Length;
  a[0] := 10; 
  var c := a; 
  if b == a { 
    assert b[0] == a[0];
    b[10] := b[0] + 1;   // ok since b == a
    assert a[10] == a[0] + 1;
  } 
  c[20] := a[14] + 2;    // ok since c == a
  assert a[20] == a[14] + 2;
  // b[0] := 4;
}


// Creating new arrays	

method NewArray() returns (a: array<int>) 
  ensures a.Length == 20 
  ensures fresh(a)
{ 
  a := new int[20]; 
  assert a.Length == 20;
  assert fresh(a);
  var b := new int[30]; 
  assert b.Length == 30;
  assert fresh(b);
  a[6] := 216; 
  b[7] := 343; 
} 		

method Caller() 
{ 
  var a := NewArray();
  assert a.Length == 20;
  assert fresh(a);
  a[8] := 512;     // allowed only if `a` is fresh 
}


// Initializing arrays 

method InitArray<T>(a: array<T>, d: T) 
  modifies a 
  ensures forall i :: 0 <= i < a.Length ==> a[i] == d
{ 
  var n := 0; 
  while n != a.Length 
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == d
    invariant forall i :: n <= i < a.Length ==> true // a[i] may be arbitrary
  {
    a[n] := d; 
    n := n + 1; 
	}
  assert forall i :: 0 <= i < a.Length ==> a[i] == d;
}


// Referring to prestate values of variables

method UpdateElements(a: array<int>) 
  requires a.Length == 10 
  modifies a 
  ensures old(a[4]) < a[4] 
  ensures a[6] <= old(a[6]) 
  ensures a[8] == old(a[8]) 
{ 
  var oldA := a[..];
  a[4] := a[4] + 3; 
  assert a[4] == oldA[4] + 3;
  a[8] := a[8] + 1; 
  a[7] := 516; 
  a[8] := a[8] - 1; 
  assert a[8] == oldA[8];
  assert a[6] == oldA[6];
  assert oldA[4] < a[4];
  assert a[6] <= oldA[6];
}


// Incrementing arrays 

method IncrementArray(a: array<int>) 
  modifies a 
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
{ 
  var n := 0; 
  while n != a.Length 
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1
    invariant forall i :: n <= i < a.Length ==> a[i] == old(a[i])
  { 
    a[n] := a[n] + 1; 
    n := n + 1; 
  }
  assert forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1;
}


// Copying arrays 

method CopyArray<T>(a: array<T>, b: array<T>) 
	  requires a.Length == b.Length 
	  modifies b 
	  ensures forall i :: 0 <= i < a.Length ==> b[i] == old(a[i])
	{ 
	  var n := 0; 
	  while n != a.Length 
      invariant 0 <= n <= a.Length
      invariant forall i :: 0 <= i < n ==> b[i] == old(a[i])
      invariant forall i :: n <= i < a.Length ==> b[i] == old(b[i])
      invariant forall i :: 0 <= i < a.Length ==> a[i] == old(a[i])
	  { 
      b[n] := a[n];
	    n := n + 1;
	  }
    assert forall i :: 0 <= i < a.Length ==> b[i] == old(a[i]);
	}

function abs(a: real) : real {if a>0.0 then a else -a}
