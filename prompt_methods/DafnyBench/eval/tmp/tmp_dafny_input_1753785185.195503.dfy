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
    forall k <- {-3, 4 }
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
    // The set is empty, so nothing happens, arr is unchanged.
    forall k <- {}
      ensures arr[i,j] == old(arr[i,j])
      ensures arr.Length0 == old(arr.Length0) && arr.Length1 == old(arr.Length1)
    {
      arr[i,j] := k;  // fine, since control will never reach here
    }
    assert arr[i,j] == old(arr[i,j]);
  }

  method K2(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Body is empty, arr is unchanged.
    forall k <- {-3, 4}
      ensures arr[i,j] == old(arr[i,j])
      ensures arr.Length0 == old(arr.Length0) && arr.Length1 == old(arr.Length1)
    {
      // No assignment
    }
    assert arr[i,j] == old(arr[i,j]);
  }

  method K3(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Only k=4 is nat in {-3,4}, and only if 4 <= i
    forall k: nat <- {-3, 4} | k <= i
      ensures (k == 4 ==> (0 <= 4 < arr.Length0 && 4 <= i ==> arr[4,j] == 50))
      ensures arr.Length0 == old(arr.Length0) && arr.Length1 == old(arr.Length1)
    {
      arr[k,j] := 50;
      assert 0 <= k < arr.Length0 && 0 <= j < arr.Length1;
      assert arr[k,j] == 50;
    }
    if i >= 4 && 4 < arr.Length0 {
      assert arr[4,j] == 50;
    }
  }

  method K4(j: int)
    requires 0 <= j < arr.Length1
    modifies arr
  {
    // Only k=4 is nat in {-3,4}, so for all i, arr[i,j] := 4
    forall i | 0 <= i < arr.Length0, k: nat <- {-3, 4}
      ensures k == 4 ==> arr[i,j] == 4
      ensures arr.Length0 == old(arr.Length0) && arr.Length1 == old(arr.Length1)
    {
      arr[i,j] := k;
      assert k == 4;
      assert arr[i,j] == 4;
    }
    assert forall i :: 0 <= i < arr.Length0 ==> arr[i,j] == 4;
  }

  method M()
  {
    var ar := new int [3,3];
    var S: set<int> := {2,0};
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
    var prev := new int[3];
    // Copy ar into prev elementwise
    var i := 0;
    while i < 3
      invariant 0 <= i <= 3
      invariant forall j :: 0 <= j < i ==> prev[j] == ar[j]
    {
      prev[i] := ar[i];
      i := i + 1;
    }
    var S: set<int> := {};
    // S is empty, so ar is unchanged
    forall k <- S
      ensures forall j :: 0 <= j < 3 ==> ar[j] == prev[j]
    {
      ar[k] := 0;
    }
    assert forall j :: 0 <= j < 3 ==> ar[j] == prev[j];
  }

  method Q() {
    var ar := new int[3,3];
    var S: set<int> := {1,2};
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
