
/* These three declarations are _abstract_ - we declare a state machine, but
 * don't actually give a definition. Dafny will assume nothing about them, so our
 * proofs below will be true for an abitrary state machine. */

type Variables
predicate Init(v: Variables)
predicate Next(v: Variables, v': Variables)

/* We'll also consider an abstract Safety predicate over states and a
 * user-supplied invariant to help prove the safety property. */

predicate Safety(v: Variables)
predicate Inv(v: Variables)

// We're going to reason about infinite executions, called behaviors here.
type Behavior = nat -> Variables

/* Now we want to prove the lemma below called SafetyAlwaysHolds. Take a look at
 * its theorem statement. To prove this lemma, we need a helper lemma for two
 * reasons: first, (because of Dafny) we need to have access to a variable for i
 * to perform induction on it, and second, (more fundamentally) we need to
 * _strengthen the induction hypothesis_ and prove `Inv(e(i))` rather than just
 * `Safety(e(i))`. */

// This is the key induction.
lemma InvHoldsTo(e: nat -> Variables, i: nat)
  requires Inv(e(0))
  requires forall i:nat :: Next(e(i), e(i+1))
  requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(e(i))
{
  if i == 0 {
    // Base case: i == 0
    // Inv(e(0)) holds by precondition
    assert Inv(e(0));
    return;
  }
  // Inductive step: assume Inv(e(i-1)), show Inv(e(i))
  // Inductive hypothesis:
  InvHoldsTo(e, i-1);
  assert Inv(e(i-1));
  assert Next(e(i-1), e(i));
  assert Inv(e(i-1)) && Next(e(i-1), e(i));
  assert Inv(e(i)); // by requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
}

ghost predicate IsBehavior(e: Behavior) {
  && Init(e(0))
  && forall i:nat :: Next(e(i), e(i+1))
}

lemma SafetyAlwaysHolds(e: Behavior)
  // In the labs, we'll prove these three conditions. Note that these properties
  // only require one or two states, not reasoning about sequences of states.
  requires forall v :: Init(v) ==> Inv(v)
  requires forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v')
  requires forall v :: Inv(v) ==> Safety(v)
  // What we get generically from those three conditions is that the safety
  // property holds for all reachable states - every state of every behavior of
  // the state machine.
  ensures IsBehavior(e) ==> forall i :: Safety(e(i))
{
  if IsBehavior(e) {
    // Prove: forall i:nat :: Safety(e(i))
    forall i:nat
      ensures Safety(e(i))
      decreases i
    {
      // Prove Inv(e(i)) holds
      // Show Inv(e(0)) holds
      assert Init(e(0));
      assert forall v :: Init(v) ==> Inv(v);
      assert Inv(e(0));
      // Show Next(e(j), e(j+1)) for all j
      assert forall j:nat :: Next(e(j), e(j+1));
      // Show Inv(v) && Next(v, v') ==> Inv(v')
      assert forall v, v' :: Inv(v) && Next(v, v') ==> Inv(v');
      // Use induction
      InvHoldsTo(e, i);
      assert Inv(e(i));
      // Inv(e(i)) ==> Safety(e(i))
      assert forall v :: Inv(v) ==> Safety(v);
      assert Safety(e(i));
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
