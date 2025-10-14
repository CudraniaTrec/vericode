// Dafny Code

method StringToCharArray(s: string) returns (a: array<char>)
    ensures a.Length == s.Length
    ensures forall i :: 0 <= i < s.Length ==> a[i] == s[i]
{
    var n := s.Length;
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