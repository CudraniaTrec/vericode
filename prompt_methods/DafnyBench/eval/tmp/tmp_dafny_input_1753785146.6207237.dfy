
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
    // Strongest annotation: k ranges over {-3,4}, so loop body runs twice, but i,j are in-bounds
    // arr[i,j] is set to 50 twice, which is fine.
    forall k <- {-3, 4}
      ensures arr[i,j] == 50
      ensures arr.Length0 == old(arr.Length0) && arr.Length1 == old(arr.Length1)
    {
      arr[i,j] := 50;
      assert 0 <= i < arr.Length0 && 0 <= j < arr.Length1;
      assert arr[i,j] == 50;
    }
    assert arr[i,j] == 50;
  }

  method K1(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    // note the absence of a modifies clause
  {
    // Strongest annotation: the set is empty, so body never executes, so arr is unchanged
    forall k <- {}
      ensures arr == old(arr)
    {
      arr[i,j] := k;  // fine, since control will never reach here
    }
    assert arr == old(arr);
  }

  method K2(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Strongest annotation: body is empty, so arr is unchanged
    forall k <- {-3, 4}
      ensures arr == old(arr)
    {
      // The following would have been an error (since this test file tests
      // compilation, we don't include the test here):
      // arr[i,j] := k;  // error: k can take on more than one value
    }
    assert arr == old(arr);
  }

  method K3(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Strongest annotation: k:nat in {-3,4} | k <= i, so k can only be 4 if 4 <= i and 0 <= 4 < arr.Length0
    // But -3 is not nat, so only k=4 if 4 <= i, or nothing if i < 4
    forall k: nat <- {-3, 4} | k <= i
      ensures k == 4 ==> (0 <= 4 < arr.Length0 && 4 <= i)
      ensures arr[k,j] == 50
      ensures arr.Length0 == old(arr.Length0) && arr.Length1 == old(arr.Length1)
    {
      arr[k,j] := 50;  // fine, since k:nat is at least 0
      assert 0 <= k < arr.Length0 && 0 <= j < arr.Length1;
      assert arr[k,j] == 50;
    }
    // If i >= 4, arr[4,j] == 50, otherwise arr unchanged
    if i >= 4 && 4 < arr.Length0 {
      assert arr[4,j] == 50;
    }
  }

  method K4(j: int)
    requires 0 <= j < arr.Length1
    modifies arr
  {
    // Strongest annotation: for all i in 0..arr.Length0-1, and k:nat in {-3,4}
    // Only k=4 is nat, so arr[i,j] := 4 for all i
    forall i | 0 <= i < arr.Length0, k: nat <- {-3, 4}
      ensures k == 4 ==> arr[i,j] == 4
      ensures arr.Length0 == old(arr.Length0) && arr.Length1 == old(arr.Length1)
    {
      arr[i,j] := k;  // fine, since k can only take on one value
      assert k == 4;
      assert arr[i,j] == 4;
    }
    // After loop, arr[0..arr.Length0-1,j] == 4
    assert forall i :: 0 <= i < arr.Length0 ==> arr[i,j] == 4;
  }

  method M()
  {
    var ar := new int [3,3];
    var S: set<int> := {2,0};
    // Strongest annotation: k in S, so k=0 or 2, ar[k,1] := 0
    forall k | k in S
      ensures ar[k,1] == 0
      ensures ar.Length0 == 3 && ar.Length1 == 3
    {
      ar[k,1]:= 0;
      assert 0 <= k < 3;
      assert ar[k,1] == 0;
    }
    assert ar[0,1] == 0 && ar[2,1] == 0;

    forall k <- S, j <- S
      ensures ar[k,j] == 0
      ensures ar.Length0 == 3 && ar.Length1 == 3
    {
      ar[k,j]:= 0;
      assert 0 <= k < 3 && 0 <= j < 3;
      assert ar[k,j] == 0;
    }
    assert ar[0,0] == 0 && ar[0,2] == 0 && ar[2,0] == 0 && ar[2,2] == 0;
  }

  method N() {
    var ar := new int[3, 3];
    ar[2,2] := 0;
    assert ar[2,2] == 0;
  }

  method P() {
    var ar := new int[3];
    var prev := ar[..];
    var S: set<int> := {};
    // Strongest annotation: S is empty, so ar is unchanged
    forall k <- S
      ensures ar == prev
    {
      ar[k] := 0;
    }
    assert ar == prev;
  }

  method Q() {
    var ar := new int[3,3];
    var S: set<int> := {1,2};
    // Strongest annotation: ar[0,0] := 0 twice, so after loop ar[0,0] == 0
    forall k <- S
      ensures ar[0,0] == 0
      ensures ar.Length0 == 3 && ar.Length1 == 3
    {
      ar[0,0] := 0;
      assert ar[0,0] == 0;
    }
    assert ar[0,0] == 0;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
