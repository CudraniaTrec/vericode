// program verifies
predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {'b', 'a', 'd'}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
{
  b := a;
  var next:int := 0;
  var aPointer:int := 0;
  var dPointer:int := |b|;

  while (next < dPointer)
    invariant 0 <= aPointer <= next <= dPointer <= |b|
    invariant multiset(b[..]) == multiset(a[..])
    invariant forall i :: 0 <= i < aPointer ==> b[i] == 'b'
    invariant forall i :: aPointer <= i < next ==> b[i] == 'a'
    invariant forall i :: dPointer <= i < |b| ==> b[i] == 'd'
    invariant forall i :: next <= i < dPointer ==> b[i] in {'a', 'b', 'd'}
  {
    if(b[next] == 'a'){
      next := next + 1;
    } 
    else if(b[next] == 'b'){
      // swap b[next] and b[aPointer]
      var tmp := b[aPointer];
      b := b[..aPointer] + [b[next]] + b[aPointer+1..next] + [tmp] + b[next+1..];
      aPointer := aPointer + 1;
      next := next + 1;
    }
    else{
      // swap b[next] and b[dPointer-1]
      dPointer := dPointer - 1;
      var tmp := b[dPointer];
      b := b[..next] + [b[dPointer]] + b[next+1..dPointer] + [b[next]] + b[dPointer+1..];
      // do not increment next here
    } 
  } 
}

function abs(a: real) : real {if a>0.0 then a else -a}
