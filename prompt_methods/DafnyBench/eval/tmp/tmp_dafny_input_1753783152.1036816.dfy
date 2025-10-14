method below_zero(operations: seq<int>) returns (s:array<int>, result:bool)
  ensures s.Length == |operations| + 1
  ensures s[0]==0
  ensures forall i :: 0 <= i < s.Length-1 ==> s[i+1]==s[i]+operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
{
  result := false;
  s := new int[|operations| + 1];
  var i := 0;
  s[i] := 0;
  while i < s.Length
    invariant 1 <= s.Length
    invariant 0 <= i <= s.Length
    invariant s[0] == 0
    invariant forall j :: 1 <= j < i ==> s[j] == s[j-1] + operations[j-1]
    invariant forall j :: i <= j < s.Length ==> s[j] == 0
  {
    if i>0{
      s[i] := s[i - 1] + operations[i - 1];
      assert s[i] == s[i-1] + operations[i-1];
    }
    i := i + 1;
  }
  i:=0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant result == false
    invariant forall j :: 0 <= j < i ==> s[j] >= 0
  {
    if s[i] < 0 {
      result := true;
      assert exists k :: 1 <= k <= |operations| && s[k] < 0;
      return;
    }
    i := i + 1;
  }
  assert forall j :: 0 <= j < s.Length ==> s[j] >= 0;
}

function abs(a: real) : real {if a>0.0 then a else -a}
