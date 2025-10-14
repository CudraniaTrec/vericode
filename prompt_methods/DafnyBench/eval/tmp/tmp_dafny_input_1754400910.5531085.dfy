
// RUN: %baredafny run %args --relax-definite-assignment --quantifier-syntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var c := new MyClass;
  c.arr := new int[10,20];
  c.K0(3, 12);
  c.K1(3, 12);
  c.K2(3, 12);
  c.K3(3, 12);
  c.K4(12);
  c.M();
  c.N();
  c.P();
  c.Q();
}

class MyClass
{
  var arr: array2<int>

  method K0(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Strongest annotation: arr[i,j] is assigned 50 exactly once, for k in {-3,4}
    // Loop invariant: arr[i,j] == 50 after the loop
    forall k <- {-3, 4} 
      ensures arr[i,j] == 50
    {
      arr[i,j] := 50;
      assert arr[i,j] == 50;
    }
    assert arr[i,j] == 50;
  }

  method K1(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    // note the absence of a modifies clause
  {
    // Strongest annotation: the loop body never executes, so nothing is modified
    assert forall k :: k !in {};
    forall k <- {} 
      ensures true
    {
      arr[i,j] := k;  // fine, since control will never reach here
    }
    assert arr[i,j] == arr[i,j];
  }

  method K2(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Strongest annotation: arr is not modified in the loop body
    forall k <- {-3, 4} 
      ensures arr[i,j] == old(arr[i,j])
    {
      // The following would have been an error (since this test file tests
      // compilation, we don't include the test here):
      // arr[i,j] := k;  // error: k can take on more than one value
      assert arr[i,j] == old(arr[i,j]);
    }
    assert arr[i,j] == old(arr[i,j]);
  }

  method K3(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Strongest annotation: arr[k,j] == 50 for all k in {-3,4} with k:nat and k <= i
    forall k: nat <- {-3, 4} | k <= i 
      ensures 0 <= k < arr.Length0 ==> arr[k,j] == 50
    {
      arr[k,j] := 50;  // fine, since k:nat is at least 0
      assert arr[k,j] == 50;
    }
    // After the loop, for all k in {-3,4} with k:nat and k <= i, arr[k,j] == 50
    assert forall k: nat :: k in {-3,4} && k <= i && 0 <= k < arr.Length0 ==> arr[k,j] == 50;
  }

  method K4(j: int)
    requires 0 <= j < arr.Length1
    modifies arr
  {
    // Strongest annotation: for all i, arr[i,j] is set to k for k in {-3,4}
    forall i | 0 <= i < arr.Length0, k: nat <- {-3, 4} 
      ensures arr[i,j] == k
    {
      arr[i,j] := k;  // fine, since k can only take on one value
      assert arr[i,j] == k;
    }
    // After the loop, for all i, arr[i,j] is either -3 or 4 (depending on k)
    assert forall i :: 0 <= i < arr.Length0 ==> (arr[i,j] == -3 || arr[i,j] == 4);
  }

  method M()
  {
    var ar := new int [3,3];
    var S: set<int> := {2,0};
    // Strongest annotation: for all k in S, ar[k,1] == 0
    forall k | k in S 
      ensures ar[k,1] == 0
    {
      ar[k,1]:= 0;
      assert ar[k,1] == 0;
    }
    assert ar[2,1] == 0 && ar[0,1] == 0;

    // Strongest annotation: for all k,j in S, ar[k,j] == 0
    forall k <- S, j <- S 
      ensures ar[k,j] == 0
    {
      ar[k,j]:= 0;
      assert ar[k,j] == 0;
    }
    assert ar[2,2] == 0 && ar[2,0] == 0 && ar[0,2] == 0 && ar[0,0] == 0;
  }

  method N() {
    var ar := new int[3, 3];
    // Strongest annotation: ar[2,2] == 0 after assignment
    ar[2,2] := 0;
    assert ar[2,2] == 0;
  }

  method P() {
    var ar := new int[3];
    var prev := ar[..];
    var S: set<int> := {};
    // Strongest annotation: ar is unchanged, since S is empty
    forall k <- S 
      ensures ar[k] == 0
    {
      ar[k] := 0;
    }
    assert ar[..] == prev;
  }

  method Q() {
    var ar := new int[3,3];
    var S: set<int> := {1,2};
    // Strongest annotation: ar[0,0] == 0 after the loop
    forall k <- S 
      ensures ar[0,0] == 0
    {
      ar[0,0] := 0;
      assert ar[0,0] == 0;
    }
    assert ar[0,0] == 0;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
