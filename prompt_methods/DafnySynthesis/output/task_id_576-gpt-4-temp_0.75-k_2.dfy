method IsSublist(sub: seq<int>, full: seq<int>) returns (isSub: bool)
{
  // An empty list is always a sublist
  if |sub| == 0 {
    isSub := true;
    return;
  }
  // sublist can't be longer than full list
  if |sub| > |full| {
    isSub := false;
    return;
  }
  // Slide a window of length |sub| over full, compare
  var found := false;
  var i := 0;
  while i <= |full| - |sub|
    invariant 0 <= i <= |full| - |sub| + 1
    invariant !found ==> forall j :: 0 <= j < i ==> full[j .. j + |sub|] != sub
  {
    if full[i .. i + |sub|] == sub {
      found := true;
      break;
    }
    i := i + 1;
  }
  isSub := found;
}