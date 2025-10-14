
// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  M0();
  M1();
  EqualityOfStrings0();
  EqualityOfStrings1();
}

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

method M0()
  ensures true
{
  // Nothing to do
}

method M1()
  ensures true
{
  var n :| ("R",n) in {("R",2),("P",1)};
  assert n == 2;
  print n, "\n";
}

method EqualityOfStrings0()
  ensures true
{
  var s1 := "abc";
  var s2 := "ab" + "c";
  assert s1 == s2;
  assert |s1| == 3;
  assert |s2| == 3;
}

method EqualityOfStrings1()
  ensures true
{
  var s1 := "abc";
  var s2 := "a" + "bc";
  assert s1 == s2;
  assert |s1| == 3;
  assert |s2| == 3;
}

method M2()
  ensures true
{
  var s := "hello";
  var t := s;
  assert s == t;
  assert |s| == |t|;
}

method M3()
  ensures true
{
  var s := "foo";
  var t := "fo" + "o";
  assert s == t;
  assert |s| == 3;
  assert |t| == 3;
}

function abs(a: real) : real {if a>0.0 then a else -a}
