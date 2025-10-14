
ghost method M1()
{
  //	assert 1 == 2;
	assume 1 == 2;
}

lemma IntersectionIsSubsetOfBoth(A: set, B: set, C: set)
	requires C == A*B
	ensures C <= A && C <= B
{
  // Strongest possible: C == A*B, so every x in C is in both A and B
  // So, C <= A and C <= B
  assert forall x :: x in C ==> x in A;
  assert forall x :: x in C ==> x in B;
}

lemma BothSetsAreSubsetsOfTheirUnion(A: set, B: set, C: set)
	requires C == A+B
	ensures A <= C && B <= C
{
  // Strongest possible: C == A+B, so every x in A or B is in C
  assert forall x :: x in A ==> x in C;
  assert forall x :: x in B ==> x in C;
}

const s0 := {3,8,1}
//var s2 := {4,5}

lemma M2()
{
	var s1 := {2,4,6,8};
	//s0 := {4,1,2};
	s1 := {};
	assert s1 == {};
}

lemma TheEmptySetIsASubsetOfAnySet(A: set, B: set)
	requires A == {}
	ensures A <= B // same as writing: B >= A
{
  // Strongest possible: The empty set is always a subset of any set
  assert forall x :: x in A ==> x in B;
}

lemma AnySetIsASubsetOfItself(A: set)
	ensures A <= A
{
  // Strongest possible: Every set is a subset of itself
  assert forall x :: x in A ==> x in A;
}

lemma TheIntersectionOfTwoSetsIsASubsetOfTheirUnion(A: set, B: set, C: set, D: set)
	requires C == A*B && D == A+B
	ensures C <= D
{
  // Strongest possible: Every x in C (A*B) is in both A and B, so in A+B
  assert forall x :: x in C ==> x in D;
}

function abs(a: real) : real {if a>0.0 then a else -a}
