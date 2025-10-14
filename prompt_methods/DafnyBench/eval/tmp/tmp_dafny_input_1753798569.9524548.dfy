
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

  assert s == s;
  Test("Identity", s == s);
  assert s == t;
  Test("ValuesIdentity", s == t);
  assert s - {1} == t - {1};
  Test("DiffIdentity", s - {1} == t - {1});
  assert s - {2} != s - {1};
  Test("DiffIdentitySelf", s - {2} != s - {1});
  assert !(s < s);
  Test("ProperSubsetIdentity", !(s < s));
  assert !(s < t);
  Test("ProperSubset", !(s < t));
  assert s <= s;
  Test("SelfSubset", s <= s);
  assert t <= s && s <= t;
  Test("OtherSubset", t <= s && s <= t);
  assert s + s == s;
  Test("UnionIdentity", s + s == s);
  assert 1 in s;
  Test("Membership", 1 in s);
  assert !(5 in s);
  Test("NonMembership1", !(5 in s));
  assert !(1 in (s - {1}));
  Test("NonMembership2", !(1 in (s - {1})));
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

  assert m1 in s1;
  Test("SeqMembership1", m1 in s1);
  assert m2 in s1;
  Test("SeqMembership2", m2 in s1);
  assert m3 in s1;
  Test("SeqMembership3", m3 in s1);
  assert !(m1 in s2);
  Test("SeqNonMembership1", !(m1 in s2));
  assert !(m4 in s1);
  Test("SeqNonMembership2", !(m4 in s1));
  assert !(m4 in s2);
  Test("SeqNonMembership3", !(m4 in s2));

  assert n1 in s1;
  Test("SeqMembershipValue1", n1 in s1);
  assert n2 in s1;
  Test("SeqMembershipValue2", n2 in s1);
  assert n3 in s1;
  Test("SeqMembershipValue3", n3 in s1);
}

method SetComprehension(s:set<uint32>)
  requires forall i :: 0 <= i < 10 ==> i in s
  requires |s| == 10
{
  var t:set<uint32> := set y:uint32 | y in s;
  assert t == s;
  Test("SetComprehensionInEquality", t == s);
  assert 0 in t;
  Test("SetComprehensionInMembership", 0 in t);
}

method LetSuchThat() {
  var s:set<uint32> := { 0, 1, 2, 3 };
  var e:uint32 :| e in s;

  //print e, "\n";
  assert e in s;
  Test("LetSuchThatMembership", e in s);
  assert e == 0 || e == 1 || e == 2 || e == 3;
  Test("LetSuchThatValue", e == 0 || e == 1 || e == 2 || e == 3);
}

method Contains() {
  var m1:seq<uint32> := [1];
  var m2:seq<uint32> := [1, 2];
  var m3:seq<uint32> := [1, 2, 3];
  var m3identical:seq<uint32> := [1, 2, 3];
  var mm := [m1, m3, m1];

  // mm = [m1, m3, m1]
  // m1 in mm: true (appears at index 0 and 2)
  // m2 in mm: false
  // m3 in mm: true (index 1)
  // m3identical in mm: true (value equality with m3 at index 1)

  assert m1 in mm;
  if m1 in mm {
    print "Membership 1: This is expected\n";
  } else {
    print "Membership 1: This is unexpected\n";
  }
  assert !(m2 in mm);
  if m2 in mm {
    print "Membership 2: This is unexpected\n";
  } else {
    print "Membership 2: This is expected\n";
  }
  assert m3 in mm;
  if m3 in mm {
    print "Membership 3: This is expected\n";
  } else {
    print "Membership 3: This is unexpected\n";
  }
  assert m3identical in mm;
  if m3identical in mm {
    print "Membership 3 value equality: This is expected\n";
  } else {
    print "Membership 3 value equality: This is unexpected\n";
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
