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
{
  // No code, nothing to annotate
}

method M1()
{
  var n :| ("R",n) in {("R",2),("P",1)};
  assert n == 2 || n == 1;
  assert ("R", n) in {("R",2),("P",1)};
  print n, "\n";
}

method EqualityOfStrings0() {
  var s1 := "abc";
  var s2 := "abc";
  assert s1 == s2;
}

method EqualityOfStrings1() {
  var s1 := "abc";
  var s2 := "ab" + "c";
  assert s1 == s2;
}

method M2()
{
  // No code, nothing to annotate
}

method M3()
{
  // No code, nothing to annotate
}

function abs(a: real) : real {if a>0.0 then a else -a}
