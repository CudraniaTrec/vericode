
method insert(line:array<char>, l:int, nl:array<char>, p:int, at:int)
  requires 0 <= l+p <= line.Length
  requires 0 <= p <= nl.Length
  requires 0 <= at <= l
  modifies line
  ensures forall i :: (0<=i<p) ==> line[at+i] == nl[i]
  ensures forall i :: (0<=i<at) ==> line[i] == old(line[i])
  ensures forall i :: (at+p<=i<l+p) ==> line[i] == old(line[i-p])
{
  ghost var initialLine := line[..];

  var i:int := l;
  while(i>at)
    invariant at <= i <= l
    invariant l + p <= line.Length
    invariant 0 <= at <= l
    invariant forall j :: l <= j < l+p ==> line[j] == initialLine[j-p]
    invariant forall j :: i <= j < l ==> line[j+p] == initialLine[j]
    invariant forall j :: 0 <= j < i ==> line[j] == initialLine[j]
  {
    i := i - 1;
    line[i+p] := line[i];
  }

  i := 0;
  while(i<p)
    invariant 0 <= i <= p
    invariant forall j :: 0 <= j < i ==> line[at + j] == nl[j]
    invariant forall j :: i <= j < p ==> at + j < line.Length ==> line[at + j] == line[at + j]
    invariant forall j :: 0 <= j < at ==> line[j] == initialLine[j]
    invariant forall j :: at+p <= j < l+p ==> line[j] == initialLine[j-p]
  {
    line[at + i] := nl[i];
    i := i + 1;
  }

}

function abs(a: real) : real {if a>0.0 then a else -a}
