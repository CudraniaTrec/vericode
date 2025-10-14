
ghost method M1()
{
  assert 1 == 2; // strongest annotation: this is false, but assume allows code to continue
  assume 1 == 2;
}

lemma IntersectionIsSubsetOfBoth(A: set, B: set, C: set)
  requires C == A*B
  ensures C <= A && C <= B
{
  // Strongest possible annotation: C is subset of A and B by definition of intersection
  assert forall x :: x in C ==> x in A && x in B;
  assert C <= A;
  assert C <= B;
}

lemma BothSetsAreSubsetsOfTheirUnion(A: set, B: set, C: set)
  requires C == A+B
  ensures A <= C && B <= C
{
  // Strongest possible annotation: every element of A and B is in C
  assert forall x :: x in A ==> x in C;
  assert forall x :: x in B ==> x in C;
  assert A <= C;
  assert B <= C;
}

const s0 := {3,8,1}
//var s2 := {4,5}

lemma M2()
{
  var s1 := {2,4,6,8};
  //s0 := {4,1,2};
  s1 := {};
  // Strongest possible annotation: s1 is now empty
  assert s1 == {};
}

lemma TheEmptySetIsASubsetOfAnySet(A: set, B: set)
  requires A == {}
  ensures A <= B // same as writing: B >= A
{
  // Strongest possible annotation: the empty set is subset of any set
  assert forall x :: x in A ==> x in B;
  assert A <= B;
}

lemma AnySetIsASubsetOfItself(A: set)
  ensures A <= A
{
  // Strongest possible annotation: reflexivity of subset
  assert forall x :: x in A ==> x in A;
  assert A <= A;
}

lemma TheIntersectionOfTwoSetsIsASubsetOfTheirUnion(A: set, B: set, C: set, D: set)
  requires C == A*B && D == A+B
  ensures C <= D
{
  // Strongest possible annotation: every element of intersection is in the union
  assert forall x :: x in C ==> x in D;
  assert C <= D;
}

function abs(a: real) : real {if a>0.0 then a else -a}
