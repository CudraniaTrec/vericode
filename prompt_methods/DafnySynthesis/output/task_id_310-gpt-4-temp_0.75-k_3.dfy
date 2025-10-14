method StringToCharArray(s: string) returns (a: array<char>)
  ensures a != null && a.Length == |s|
  ensures forall i :: 0 <= i < a.Length ==> a[i] == s[i]
{
  var n := |s|;
  a := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == s[j]
  {
    a[i] := s[i];
    i := i + 1;
  }
}