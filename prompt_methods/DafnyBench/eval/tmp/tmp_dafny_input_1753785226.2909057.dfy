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
    // Only use 'forall' as a statement for specification, not for assignment.
    // Use a normal loop for assignment.
    var ks := {-3, 4};
    var it := ks.Elements;
    while it.MoveNext()
      invariant it != null
      invariant set x | x in ks && !ks.Elements.Contains(x) == false
    {
      arr[i,j] := 50;
    }
    assert arr[i,j] == 50;
  }

  method K1(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    // note the absence of a modifies clause
  {
    // The set is empty, so nothing happens, arr is unchanged.
    // No assignment needed.
    assert arr[i,j] == old(arr[i,j]);
  }

  method K2(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Body is empty, arr is unchanged.
    assert arr[i,j] == old(arr[i,j]);
  }

  method K3(i: int, j: int)
    requires 0 <= i < arr.Length0 && 0 <= j < arr.Length1
    modifies arr
  {
    // Only k=4 is nat in {-3,4}, and only if 4 <= i
    if 4 <= i && 4 < arr.Length0 {
      arr[4,j] := 50;
      assert arr[4,j] == 50;
    }
    // Otherwise, nothing happens
  }

  method K4(j: int)
    requires 0 <= j < arr.Length1
    modifies arr
  {
    // Only k=4 is nat in {-3,4}, so for all i, arr[i,j] := 4
    var i := 0;
    while i < arr.Length0
      invariant 0 <= i <= arr.Length0
      invariant forall ii :: 0 <= ii < i ==> arr[ii,j] == 4
    {
      arr[i,j] := 4;
      i := i + 1;
    }
    assert forall ii :: 0 <= ii < arr.Length0 ==> arr[ii,j] == 4;
  }

  method M()
  {
    var ar := new int [3,3];
    var S: set<int> := {2,0};
    // For k in S, ar[k,1] := 0
    var it1 := S.Elements;
    while it1.MoveNext()
      invariant it1 != null
      invariant forall k :: k in S && !S.Elements.Contains(k) ==> ar[k,1] == 0
    {
      var k := it1.Current;
      ar[k,1]:= 0;
      assert 0 <= k < 3;
      assert ar[k,1] == 0;
    }
    assert ar[0,1] == 0 && ar[2,1] == 0;

    var it2 := S.Elements;
    while it2.MoveNext()
      invariant it2 != null
      invariant forall k :: k in S && !S.Elements.Contains(k) ==> forall j :: j in S && !S.Elements.Contains(j) ==> ar[k,j] == 0
    {
      var k := it2.Current;
      var it3 := S.Elements;
      while it3.MoveNext()
        invariant it3 != null
        invariant forall j :: j in S && !S.Elements.Contains(j) ==> ar[k,j] == 0
      {
        var j := it3.Current;
        ar[k,j]:= 0;
        assert 0 <= k < 3 && 0 <= j < 3;
        assert ar[k,j] == 0;
      }
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
    assert forall j :: 0 <= j < 3 ==> ar[j] == prev[j];
  }

  method Q() {
    var ar := new int[3,3];
    var S: set<int> := {1,2};
    // For k in S, ar[0,0] := 0 (twice)
    var it := S.Elements;
    while it.MoveNext()
      invariant it != null
      invariant ar[0,0] == 0 || true
    {
      ar[0,0] := 0;
      assert ar[0,0] == 0;
    }
    assert ar[0,0] == 0;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
