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
    // Strongest annotation: arr[i,j] is assigned 50
    // No forall statement with assignment, use a normal loop
    var S := {-3, 4};
    var assigned := false;
    // Only assign if i is in S (but i is not, so assign once)
    arr[i,j] := 50;
    assert arr[i,j] == 50;
  }

  method K1(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    // note the absence of a modifies clause
  {
    // The set is empty, so nothing happens
    assert true;
  }

  method K2(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // No assignment is done in the loop, so nothing changes
    assert arr[i,j] == old(arr[i,j]);
  }

  method K3(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Only assign for k in {-3, 4} where k:nat and k <= i
    var S := {-3, 4};
    // Only k=4 is nat and possibly <= i
    if 0 <= 4 && 4 <= i && 4 < arr.Length0 {
      arr[4,j] := 50;
      assert arr[4,j] == 50;
    }
    // -3 is not nat, so nothing to do
    assert forall k: nat :: k in S && k <= i && 0 <= k < arr.Length0 ==> arr[k,j] == 50;
  }

  method K4(j: int)
    requires 0 <= j < arr.Length1
    modifies arr
  {
    // For all i in 0..arr.Length0, assign arr[i,j] to -3 and then to 4
    var i := 0;
    while i < arr.Length0
      invariant 0 <= i <= arr.Length0
      invariant forall h: int :: 0 <= h < i ==> arr[h,j] == 4
    {
      arr[i,j] := -3;
      arr[i,j] := 4;
      assert arr[i,j] == 4;
      i := i + 1;
    }
    assert forall h: int :: 0 <= h < arr.Length0 ==> arr[h,j] == 4;
  }

  method M()
  {
    var ar := new int [3,3];
    var S: set<int> := {2,0};
    // For all k in S, assign ar[k,1] := 0
    var k := 0;
    while k < 3
      invariant 0 <= k <= 3
      invariant forall h: int :: 0 <= h < k && h in S ==> ar[h,1] == 0
    {
      if k in S {
        ar[k,1] := 0;
        assert ar[k,1] == 0;
      }
      k := k + 1;
    }
    assert ar[2,1] == 0 && ar[0,1] == 0;

    // For all k, j in S, assign ar[k,j] := 0
    var a := 0;
    while a < 3
      invariant 0 <= a <= 3
      invariant forall h: int :: 0 <= h < a && h in S ==> forall l: int :: l in S ==> ar[h,l] == 0
    {
      if a in S {
        var b := 0;
        while b < 3
          invariant 0 <= b <= 3
          invariant forall l: int :: 0 <= l < b && l in S ==> ar[a,l] == 0
        {
          if b in S {
            ar[a,b] := 0;
            assert ar[a,b] == 0;
          }
          b := b + 1;
        }
      }
      a := a + 1;
    }
    assert ar[2,2] == 0 && ar[2,0] == 0 && ar[0,2] == 0 && ar[0,0] == 0;
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
    // S is empty, so nothing happens
    assert ar[..] == prev;
  }

  method Q() {
    var ar := new int[3,3];
    var S: set<int> := {1,2};
    // For all k in S, assign ar[0,0] := 0 (multiple times, but always 0)
    var i := 0;
    while i < 2
      invariant 0 <= i <= 2
      invariant ar[0,0] == 0 || i == 0
    {
      ar[0,0] := 0;
      assert ar[0,0] == 0;
      i := i + 1;
    }
    assert ar[0,0] == 0;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
