
module Ex {
  // This simple example illustrates what the process of looking for an
  // inductive invariant might look like.

  datatype Variables = Variables(p1: bool, p2: bool, p3: bool, p4: bool)

  ghost predicate Init(v: Variables) {
    && !v.p1
    && !v.p2
    && !v.p3
    && !v.p4
  }

  // The state machine starts out with all four booleans false, and it "turns
  // on" p1, p2, p3, and p4 in order. The safety property says p4 ==> p1;
  // proving this requires a stronger inductive invariant.

  datatype Step =
    | Step1
    | Step2
    | Step3
    | Step4
    | Noop

  ghost predicate NextStep(v: Variables, v': Variables, step: Step)
  {
    match step {
      // ordinarily we'd have a predicate for each step, but in this simple
      // example it's easier to see everything written in one place
      case Step1 =>
        !v.p1 && v' == v.(p1 := true)
      case Step2 =>
        v.p1 && v' == v.(p2 := true)
      case Step3 =>
        v.p2 && v' == v.(p3 := true)
      case Step4 =>
        v.p3 && v' == v.(p4 := true)
      case Noop => v' == v
    }
  }

  ghost predicate Next(v: Variables, v': Variables)
  {
    exists step: Step :: NextStep(v, v', step)
  }

  ghost predicate Safety(v: Variables)
  {
    v.p4 ==> v.p1
  }

  ghost predicate Inv(v: Variables)
  {
    // SOLUTION
    // This is one approach: prove implications that go all the way back to the
    // beginning, trying to slowly work our way up to something inductive.
    && Safety(v)
    && (v.p3 ==> v.p1)
    && (v.p2 ==> v.p1)
    // END
  }

  lemma InvInductive(v: Variables, v': Variables)
    requires Inv(v) && Next(v, v')
    ensures Inv(v')
  {
    // SOLUTION
    // This :| syntax is called "assign-such-that". Think of it as telling Dafny
    // to assign step a value such that NextStep(v, v', step) (the predicate on
    // the RHS) holds. What Dafny will do is first prove there exists such a
    // step, then bind an arbitrary value to step where NextStep(v, v', step)
    // holds for the remainder of the proof.
    var step :| NextStep(v, v', step);
    // END
    match step {
      case Step1 => { 
        // Step1: !v.p1 && v' == v.(p1 := true)
        // v'.p1 == true, v'.p2 == v.p2, v'.p3 == v.p3, v'.p4 == v.p4
        // Safety(v'): v'.p4 ==> v'.p1
        // If v'.p4, then v'.p4 == v.p4, and v'.p1 == true, so holds.
        // (v'.p3 ==> v'.p1): v'.p3 == v.p3, v'.p1 == true, so holds.
        // (v'.p2 ==> v'.p1): v'.p2 == v.p2, v'.p1 == true, so holds.
        assert v'.p1;
        return; 
      }
      case Step2 => { 
        // Step2: v.p1 && v' == v.(p2 := true)
        // v'.p1 == v.p1 == true, v'.p2 == true, v'.p3 == v.p3, v'.p4 == v.p4
        // Safety(v'): v'.p4 ==> v'.p1
        // (v'.p3 ==> v'.p1): v'.p3 == v.p3, v'.p1 == true, so holds.
        // (v'.p2 ==> v'.p1): v'.p2 == true, v'.p1 == true, so holds.
        assert v'.p1;
        return; 
      }
      case Step3 => { 
        // Step3: v.p2 && v' == v.(p3 := true)
        // v'.p1 == v.p1, v'.p2 == v.p2 == true, v'.p3 == true, v'.p4 == v.p4
        // Safety(v'): v'.p4 ==> v'.p1
        // (v'.p3 ==> v'.p1): v'.p3 == true ==> v'.p1 == v.p1
        // But v'.p3 == true, so need v'.p1 == v.p1
        // But Inv(v): (v.p3 ==> v.p1), so if v.p3, then v.p1
        // But v'.p3 == true, so v.p3 can be true or false
        // If v.p3 == true, then v.p1 == true by Inv(v)
        // If v.p3 == false, then v'.p3 == true, so transition happened
        // But step3 only happens if v.p2 == true, so v.p2 == true
        // Inv(v): (v.p2 ==> v.p1), so v.p1 == true
        // So in all cases, v'.p1 == v.p1 == true
        assert v'.p1;
        return; 
      }
      case Step4 => {
        // Step4: v.p3 && v' == v.(p4 := true)
        // v'.p1 == v.p1, v'.p2 == v.p2, v'.p3 == v.p3 == true, v'.p4 == true
        // Safety(v'): v'.p4 ==> v'.p1
        // v'.p4 == true, so need v'.p1 == v.p1
        // But v'.p3 == true, so Inv(v): (v.p3 ==> v.p1), so v.p1 == true
        // (v'.p3 ==> v'.p1): v'.p3 == true, v'.p1 == v.p1 == true
        // (v'.p2 ==> v'.p1): v'.p2 == v.p2, if v.p2 then v.p1 == true by Inv(v)
        assert v'.p1;
        return;
        // END
      }
      case Noop => { 
        // No state change
        return; 
      }
    }
  }

  lemma InvSafe(v: Variables)
    ensures Inv(v) ==> Safety(v)
  {
    return;
  }

  // This is the main inductive proof of Safety, but we moved all the difficult
  // reasoning to the lemmas above.
  lemma SafetyHolds(v: Variables, v': Variables)
    ensures Init(v) ==> Inv(v)
    ensures Inv(v) && Next(v, v') ==> Inv(v')
    ensures Inv(v) ==> Safety(v)
  {
    if Inv(v) && Next(v, v') {
      InvInductive(v, v');
    }
    InvSafe(v);
  }

  // SOLUTION
  // Instead of worrying about Safety, we can approach invariants by starting
  // with properties that should hold in all reachable states. The advantage of
  // this approach is that we can "checkpoint" our work of writing an invariant
  // that characterizes reachable states. The disadvantage is that we might
  // prove properties that don't help with safety and waste time.
  //
  // Recall that an invariant may have a counterexample to induction (CTI): a
  // way to start in a state satisfying the invariant and transition out of it.
  // If the invariant really holds, then a CTI simply reflects an unreachable
  // state, one that we should try to eliminate by strengthening the invariant.
  // If we find a "self-inductive" property Inv that satisfies Init(v) ==>
  // Inv(v) and Inv(v) && Next(v, v') ==> Inv(v'), then we can extend it without
  // fear of breaking inductiveness: in proving Inv(v) && Inv2(v) && Next(v, v')
  // ==> Inv(v') && Inv2(v'), notice that we can immediately prove Inv(v').
  // However, we've also made progress: in proving Inv2(v'), we get to know
  // Inv(v). This may rule out some CTIs, and eventually will be enough to prove
  // Inv2 is inductive.
  //
  // Notice that the above discussion involved identifying a self-inductive
  // invariant without trying to prove a safety property. This is one way to go
  // about proving safety: start by proving "easy" properties that hold in
  // reachable states. This will reduce the burden of getting CTIs (or failed
  // proofs). However, don't spend all your time proving properties about
  // reachable states: there will likely be properties that really are
  // invariants, but (a) the proof is complicated and (b) they don't help you
  // prove safety.

  predicate Inv2(v: Variables) {
    // each of these conjuncts is individually "self-inductive", but all of them
    // are needed together to actually prove safety
    && (v.p2 ==> v.p1)
    && (v.p3 ==> v.p2)
    && (v.p4 ==> v.p3)
  }

  lemma Inv2Holds(v: Variables, v': Variables)
    ensures Init(v) ==> Inv2(v)
    ensures Inv2(v) && Next(v, v') ==> Inv2(v')
  {
    if Inv2(v) && Next(v, v') {
      var step :| NextStep(v, v', step);
      match step {
        case Step1 => { 
          // Step1: !v.p1 && v' == v.(p1 := true)
          // v'.p1 == true, v'.p2 == v.p2, v'.p3 == v.p3, v'.p4 == v.p4
          // (v'.p2 ==> v'.p1): if v'.p2, then v.p2, so v'.p1 == true
          // (v'.p3 ==> v'.p2): v'.p3 == v.p3, v'.p2 == v.p2, so if v.p3 then v.p2, so holds by Inv2(v)
          // (v'.p4 ==> v'.p3): v'.p4 == v.p4, v'.p3 == v.p3, so if v.p4 then v.p3, so holds by Inv2(v)
          assert (v'.p2 ==> v'.p1);
          assert (v'.p3 ==> v'.p2);
          assert (v'.p4 ==> v'.p3);
          return; 
        }
        case Step2 => { 
          // Step2: v.p1 && v' == v.(p2 := true)
          // v'.p1 == v.p1 == true, v'.p2 == true, v'.p3 == v.p3, v'.p4 == v.p4
          // (v'.p2 ==> v'.p1): v'.p2 == true, v'.p1 == true
          // (v'.p3 ==> v'.p2): v'.p3 == v.p3, v'.p2 == true, so holds
          // (v'.p4 ==> v'.p3): v'.p4 == v.p4, v'.p3 == v.p3, so if v.p4 then v.p3, so holds by Inv2(v)
          assert (v'.p2 ==> v'.p1);
          assert (v'.p3 ==> v'.p2);
          assert (v'.p4 ==> v'.p3);
          return; 
        }
        case Step3 => { 
          // Step3: v.p2 && v' == v.(p3 := true)
          // v'.p1 == v.p1, v'.p2 == v.p2 == true, v'.p3 == true, v'.p4 == v.p4
          // (v'.p2 ==> v'.p1): v'.p2 == true, v'.p1 == v.p1
          // (v'.p3 ==> v'.p2): v'.p3 == true, v'.p2 == true
          // (v'.p4 ==> v'.p3): v'.p4 == v.p4, v'.p3 == true, so holds
          assert (v'.p2 ==> v'.p1);
          assert (v'.p3 ==> v'.p2);
          assert (v'.p4 ==> v'.p3);
          return; 
        }
        case Step4 => { 
          // Step4: v.p3 && v' == v.(p4 := true)
          // v'.p1 == v.p1, v'.p2 == v.p2, v'.p3 == v.p3 == true, v'.p4 == true
          // (v'.p2 ==> v'.p1): v'.p2 == v.p2, v'.p1 == v.p1, so if v.p2 then v.p1, holds by Inv2(v)
          // (v'.p3 ==> v'.p2): v'.p3 == true, v'.p2 == v.p2, so need v.p2 == true
          // But step4 only possible if v.p3 == true, so v.p3 == true, so Inv2(v): (v.p3 ==> v.p2), so v.p2 == true
          // (v'.p4 ==> v'.p3): v'.p4 == true, v'.p3 == true
          assert (v'.p2 ==> v'.p1);
          assert (v'.p3 ==> v'.p2);
          assert (v'.p4 ==> v'.p3);
          return; 
        }
        case Noop => { 
          // No state change
          return; 
        }
      }
    }
  }
  // END
}

function abs(a: real) : real {if a>0.0 then a else -a}
