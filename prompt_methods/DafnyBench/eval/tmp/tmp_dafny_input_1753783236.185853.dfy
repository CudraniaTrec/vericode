method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]

{
  if len == 0 { return dest; }
  r := new int[dest.Length];
  var i: nat := 0;
  // Copy all of dest into r
  while (i < dest.Length)
    invariant 0 <= i <= dest.Length
    invariant r.Length == dest.Length
    invariant forall j :: 0 <= j < i ==> r[j] == dest[j]
    invariant forall j :: i <= j < dest.Length ==> r[j] == 0
  {
    r[i] := dest[i];
    i := i + 1;
  }
  i := 0;
  // Overwrite r[dStart..dStart+len) with src[sStart..sStart+len)
  while (i < len)
    invariant 0 <= i <= len
    invariant r.Length == dest.Length
    invariant forall j :: 0 <= j < i ==> r[dStart + j] == src[sStart + j]
    invariant forall j :: i <= j < len ==> r[dStart + j] == dest[dStart + j]
    invariant forall j :: 0 <= j < dStart ==> r[j] == dest[j]
    invariant forall j :: dStart + len <= j < dest.Length ==> r[j] == dest[j]
  {
    r[dStart + i] := src[sStart + i];
    i := i + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
