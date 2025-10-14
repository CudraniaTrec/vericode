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
        assert IsSubset(A, B);
        assert x in A;
        assert x in B; // by IsSubset(A, B)
        // By Pre2: IsSubset(B, C), so x in B ==> x in C
        assert IsSubset(B, C);
        assert x in C; // by IsSubset(B, C)
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
