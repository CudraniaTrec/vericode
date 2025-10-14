// RUN: /compile:0 /nologo

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
{
  var b :| b in B && b !in A;
  var B' := B - {b};
  if A < B' {
    // |B'| == |B| - 1, and A < B'
    // decreases |B| - |A|
    CardinalitySubsetLt(A, B');
  } else {
    // A == B'
    // So |A| == |B| - 1
    // So |A| < |B|
  }
}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
{
  count := 0;
  var I := {};
  var S := {};
  var switch := false;

  while count < |P| - 1
    invariant 0 <= count <= |P| - 1
    invariant I <= P
    invariant S <= I
    invariant Special in P
    invariant |I| <= |P|
    invariant |S| <= |I|
    invariant count == |S|
    invariant (forall x :: x in S ==> x != Special)
    invariant (forall x :: x in S ==> x in I)
    decreases |P| - count
  { 
    var p :| p in P - I;
    I := I + {p};

    if p == Special {
      if switch {
        switch := false;
        count := count + 1;
      }
    } else {
      if p !in S && !switch {
        S := S + {p};
        switch := true;
      }
    }
  }  

  // S < I always holds: S is subset of I, and S != I since |S| = count < |P|-1 <= |I|
  CardinalitySubsetLt(S, I);

  if I < P {
    CardinalitySubsetLt(I, P);
  }

}

function abs(a: real) : real {if a>0.0 then a else -a}
