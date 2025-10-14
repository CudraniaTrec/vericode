
method allDigits(s: string) returns (result: bool)
ensures  result <==> (forall i :: 0 <= i < |s| ==> s[i] in "0123456789")
{
  result := true;
  var i: int;
  i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result ==> (forall j :: 0 <= j < i ==> s[j] in "0123456789")
    invariant !result ==> (exists j :: 0 <= j < i && s[j] !in "0123456789")
  {
    if !(s[i] in "0123456789") {
      result := false;
      return false;
    }
    i := i + 1;
  }
  // At this point, i == |s|
  assert (forall j :: 0 <= j < |s| ==> s[j] in "0123456789");
}

function abs(a: real) : real {if a>0.0 then a else -a}
