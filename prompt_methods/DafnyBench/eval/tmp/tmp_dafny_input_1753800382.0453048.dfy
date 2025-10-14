
// RUN: /compile:0 /nologo

method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
{
  var b :| b in B && b !in A;
  assert b in B && b !in A;
  var B' := B - {b};
  if A < B' {
    assert B' < B;
    assert |B'| == |B| - 1;
    assert A < B';
    CardinalitySubsetLt(A, B');
    assert |A| < |B'|;
    assert |B'| < |B|;
    assert |A| < |B|;
  } else {
    assert A == B';
    assert |A| == |B| - 1;
    assert |A| < |B|;
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
    invariant Special in P ==> (switch ==> Special !in S)
    invariant |I| <= |P|
    invariant |S| <= |I|
    invariant count == |S|
    invariant (forall x :: x in S ==> x != Special)
    decreases |P| - 1 - count
  { 
    var p :| p in P;
    assert p in P;
    I := I + {p};
    assert I <= P;

    if p == Special {
      if switch {
        switch := false;
        count := count + 1;
        assert count <= |P| - 1;
      }
    } else {
      if p !in S && !switch {
        S := S + {p};
        assert S <= I;
        switch := true;
        assert count == |S| - 1;
      }
    }
    assert count == |S|;
  }  

  assert S < I;
  CardinalitySubsetLt(S, I);

  if I < P {
    CardinalitySubsetLt(I, P);
  }

}

function abs(a: real) : real {if a>0.0 then a else -a}
