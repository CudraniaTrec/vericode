
method iter_copy<T(0)>(s: array<T>) returns (t: array<T>)
  ensures s.Length==t.Length
  ensures forall i::0<=i<s.Length ==> s[i]==t[i]
{
  t := new T[s.Length];
  var i:= 0;
  while (i < s.Length)
    invariant 0 <= i <= s.Length
    invariant t.Length == s.Length
    invariant forall j :: 0 <= j < i ==> t[j] == s[j]
  {
    t[i] := s[i];
    i:=i+1;
  }
  assert t.Length == s.Length;
  assert forall i :: 0 <= i < s.Length ==> t[i] == s[i];
}

function abs(a: real) : real {if a>0.0 then a else -a}
