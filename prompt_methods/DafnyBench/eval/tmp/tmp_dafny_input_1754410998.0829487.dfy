///////////////////////////
// Lemma to prove Transitive
// Got A<B, B<C.
// Prove A<C
///////////////////////////
predicate IsSubset(A: set, B: set) // <=
{
	forall n :: n in A ==> n in B // same as the next line
	//forall n :: if n in A then n in B else true // same as "A <= B"
}
// lemma - משפט
// subsetIsTransitive - lemma name.
// (A: set, B: set, C: set) - parameters using in lemma.
// "A" - parameter name, ": set " - parameter type (set = group).
lemma subsetIsTransitive(A: set, B: set, C: set)
    // requires - הנתון/הדרישה של הטענה 
    // "Pre1" - label,require התוית של 
    // "IsSubset" - function name. "(A, B)" function parameters
    requires Pre1 : IsSubset(A, B)
    requires Pre2 : IsSubset(B, C)
    // ensures - ״מבטיח לי״- צריך להוכיח
    ensures IsSubset(A, C)
// Start of ensure - תחילת ההוכחה
{
    // forall - לכל X
    // "x in A" - כך שx שייך ל A,
    // ensures x in C - מבטיח שX שייך לC
    forall x | x in A ensures x in C {
        // By Pre1: IsSubset(A, B), so x in A ==> x in B
        // Unfold the definition of IsSubset(A, B) and IsSubset(B, C)
        // Need to use the definition directly
        // IsSubset(A, B) == forall n :: n in A ==> n in B
        // IsSubset(B, C) == forall n :: n in B ==> n in C
        // So, since x in A, and IsSubset(A, B), x in B
        assert forall n :: n in A ==> n in B;
        assert x in B;
        // Now, x in B and IsSubset(B, C), so x in C
        assert forall n :: n in B ==> n in C;
        assert x in C;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
