
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = i:int | 0 <= i < 0x100000000

datatype Example0 = Example0(u:uint32, b:bool)

method Test0(e0:Example0)
{
  var s := { e0 };
  assert e0 in s;
  assert |s| == 1;
}

datatype Example1 = Ex1a(u:uint32) |  Ex1b(b:bool)
method Test1(t0:Example1)
{
  var t := { t0 };
  assert t0 in t;
  assert |t| == 1;
}

method Test(name:string, b:bool)
  requires b
{
  if b {
    print name, ": This is expected\n";
  } else {
    print name, ": This is *** UNEXPECTED *** !!!!\n";
  }
}

method Basic() {
  var s:set<uint32> := {1, 2, 3, 4};
  var t:set<uint32> := {1, 2, 3, 4};

  Test("Identity", s == s);
  Test("ValuesIdentity", s == t);
  Test("DiffIdentity", s - {1} == t - {1});
  Test("DiffIdentitySelf", s - {2} != s - {1});
  Test("ProperSubsetIdentity", !(s < s));
  Test("ProperSubset", !(s < t));
  Test("SelfSubset", s <= s);
  Test("OtherSubset", t <= s && s <= t);
  Test("UnionIdentity", s + s == s);
  Test("Membership", 1 in s);
  Test("NonMembership1", !(5 in s));
  Test("NonMembership2", !(1 in (s - {1})));
  assert |s| == 4;
  assert s == t;
  assert (s - {1}) == (t - {1});
  assert (s - {2}) != (s - {1});
  assert !(s < s);
  assert !(s < t);
  assert s <= s;
  assert t <= s && s <= t;
  assert s + s == s;
  assert 1 in s;
  assert !(5 in s);
  assert !(1 in (s - {1}));
}

method SetSeq() {
  var m1:seq<uint32> := [1];
  var m2:seq<uint32> := [1, 2];
  var m3:seq<uint32> := [1, 2, 3];
  var m4:seq<uint32> := [1, 2, 3, 4];
  var n1:seq<uint32> := [1];
  var n2:seq<uint32> := [1, 2];
  var n3:seq<uint32> := [1, 2, 3];

  var s1:set<seq<uint32>> := { m1, m2, m3 };
  var s2:set<seq<uint32>> := s1 - { m1 };

  Test("SeqMembership1", m1 in s1);
  Test("SeqMembership2", m2 in s1);
  Test("SeqMembership3", m3 in s1);
  Test("SeqNonMembership1", !(m1 in s2));
  Test("SeqNonMembership2", !(m4 in s1));
  Test("SeqNonMembership3", !(m4 in s2));

  Test("SeqMembershipValue1", n1 in s1);
  Test("SeqMembershipValue2", n2 in s1);
  Test("SeqMembershipValue3", n3 in s1);

  assert m1 in s1;
  assert m2 in s1;
  assert m3 in s1;
  assert !(m1 in s2);
  assert !(m4 in s1);
  assert !(m4 in s2);
  assert n1 in s1;
  assert n2 in s1;
  assert n3 in s1;
}

method SetComprehension(s:set<uint32>)
  requires forall i :: 0 <= i < 10 ==> i in s
  requires |s| == 10
{
  var t:set<uint32> := set y:uint32 | y in s;
  Test("SetComprehensionInEquality", t == s);
  Test("SetComprehensionInMembership", 0 in t);
  assert t == s;
  assert 0 in t;
  assert |t| == 10;
  assert forall i :: 0 <= i < 10 ==> i in t;
}

method LetSuchThat() {
  var s:set<uint32> := { 0, 1, 2, 3 };
  var e:uint32 :| e in s;

  //print e, "\n";
  Test("LetSuchThatMembership", e in s);
  Test("LetSuchThatValue", e == 0 || e == 1 || e == 2 || e == 3);
  assert e in s;
  assert e == 0 || e == 1 || e == 2 || e == 3;
}

method Contains() {
  var m1:seq<uint32> := [1];
  var m2:seq<uint32> := [1, 2];
  var m3:seq<uint32> := [1, 2, 3];
  var m3identical:seq<uint32> := [1, 2, 3];
  var mm := [m1, m3, m1];

  // Loop to check membership
  var found1 := false;
  var found2 := false;
  var found3 := false;
  var found3identical := false;
  var i := 0;
  while i < |mm|
    invariant 0 <= i <= |mm|
    invariant found1 == (exists j :: 0 <= j < i && mm[j] == m1)
    invariant found2 == (exists j :: 0 <= j < i && mm[j] == m2)
    invariant found3 == (exists j :: 0 <= j < i && mm[j] == m3)
    invariant found3identical == (exists j :: 0 <= j < i && mm[j] == m3identical)
  {
    if mm[i] == m1 { found1 := true; }
    if mm[i] == m2 { found2 := true; }
    if mm[i] == m3 { found3 := true; }
    if mm[i] == m3identical { found3identical := true; }
    i := i + 1;
  }
  if m1 in mm {
    print "Membership 1: This is expected\n";
    assert found1;
  } else {
    print "Membership 1: This is unexpected\n";
    assert !found1;
  }
  if m2 in mm {
    print "Membership 2: This is unexpected\n";
    assert found2;
  } else {
    print "Membership 2: This is expected\n";
    assert !found2;
  }
  if m3 in mm {
    print "Membership 3: This is expected\n";
    assert found3;
  } else {
    print "Membership 3: This is unexpected\n";
    assert !found3;
  }
  if m3identical in mm {
    print "Membership 3 value equality: This is expected\n";
    assert found3identical;
  } else {
    print "Membership 3 value equality: This is unexpected\n";
    assert !found3identical;
  }
}

method Main() {
  Basic();
  SetSeq();
  var s := { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  SetComprehension(s);
  LetSuchThat();
}

function abs(a: real) : real {if a>0.0 then a else -a}
