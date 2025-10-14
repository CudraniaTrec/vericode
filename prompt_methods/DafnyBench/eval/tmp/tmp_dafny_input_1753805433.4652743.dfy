
// Ported from ivy/examples/ivy/toy_consensus.ivy.

// Ivy only supports first-order logic, which is limited (perhaps in surprising
// ways). In this model of consensus, we use some tricks to model quorums in
// first-order logic without getting into the arithmetic of why sets of n/2+1
// nodes intersect.

type Node(==)
type Quorum(==)
type Choice(==)

ghost predicate Member(n: Node, q: Quorum)

// axiom: any two quorums intersect in at least one node
// SOLUTION
// note we give this without proof: this is in general dangerous! However, here
// we believe it is possible to have Node and Quorum types with this property.
//
// The way we might realize that is to have Node be a finite type (one value for
// each node in the system) and Quorum to capture any subset with strictly more
// than half the nodes. Such a setup guarantees that any two quorums intersect.
// END
lemma {:axiom} QuorumIntersect(q1: Quorum, q2: Quorum) returns (n: Node)
  ensures Member(n, q1) && Member(n, q2)

datatype Variables = Variables(
  votes: map<Node, set<Choice>>,
  // this is one reason why this is "toy" consensus: the decision is a global
  // variable rather than being decided at each node individually
  decision: set<Choice>
)
{
  ghost predicate WF()
  {
    && (forall n:Node :: n in votes)
  }
}

datatype Step =
  | CastVoteStep(n: Node, c: Choice)
  | DecideStep(c: Choice, q: Quorum)

ghost predicate CastVote(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.CastVoteStep?
{
  var n := step.n;
  && (v.votes[n] == {})
     // learn to read these "functional updates" of maps/sequences:
     // this is like v.votes[n] += {step.c} if that was supported
  && (v' == v.(votes := v.votes[n := v.votes[n] + {step.c}]))
}

ghost predicate Decide(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.DecideStep?
{
  // if all nodes of a quorum have voted for a value, then that value can be a
  // decision
  && (forall n: Node | Member(n, step.q) :: step.c in v.votes[n])
  && v' == v.(decision := v.decision + {step.c})
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  && v.WF()
  && match step {
       case CastVoteStep(_, _) => CastVote(v, v', step)
       case DecideStep(_, _) => Decide(v, v', step)
     }
}

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{
  // Strongest annotation: show that for each case, v'1 == v'2
  if step.CastVoteStep? {
    // Both v'1 and v'2 are v.(votes := v.votes[step.n := v.votes[step.n] + {step.c}])
    assert v'1 == v.(votes := v.votes[step.n := v.votes[step.n] + {step.c}]);
    assert v'2 == v.(votes := v.votes[step.n := v.votes[step.n] + {step.c}]);
    assert v'1 == v'2;
  } else if step.DecideStep? {
    // Both v'1 and v'2 are v.(decision := v.decision + {step.c})
    assert v'1 == v.(decision := v.decision + {step.c});
    assert v'2 == v.(decision := v.decision + {step.c});
    assert v'1 == v'2;
  }
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

ghost predicate Init(v: Variables) {
  && v.WF()
  && (forall n :: v.votes[n] == {})
  && v.decision == {}
}

ghost predicate Safety(v: Variables) {
  forall c1, c2 :: c1 in v.decision && c2 in v.decision ==> c1 == c2
}

// SOLUTION
ghost predicate ChoiceQuorum(v: Variables, q: Quorum, c: Choice)
  requires v.WF()
{
  forall n :: Member(n, q) ==> c in v.votes[n]
}

ghost predicate Inv(v: Variables) {
  && v.WF()
  && Safety(v)
  && (forall n, v1, v2 :: v1 in v.votes[n] && v2 in v.votes[n] ==> v1 == v2)
  && (forall c :: c in v.decision ==> exists q:Quorum :: ChoiceQuorum(v, q, c))
}
// END

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{
  // Strongest annotation: show all conjuncts of Inv hold
  // 1. v.WF()
  assert v.WF();
  // 2. Safety(v): v.decision == {} so trivially holds
  assert forall c1, c2 :: c1 in v.decision && c2 in v.decision ==> c1 == c2;
  // 3. forall n, v1, v2 :: v1 in v.votes[n] && v2 in v.votes[n] ==> v1 == v2
  assert forall n, v1, v2 :: v1 in v.votes[n] && v2 in v.votes[n] ==> v1 == v2;
  // 4. forall c :: c in v.decision ==> exists q:Quorum :: ChoiceQuorum(v, q, c)
  assert forall c :: c in v.decision ==> exists q:Quorum :: ChoiceQuorum(v, q, c);
}

lemma InvInductive(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  var step :| NextStep(v, v', step);
  // SOLUTION
  match step {
    case CastVoteStep(n, c) => {
      // Strongest annotation: v'.decision == v.decision, v'.votes[n] = v.votes[n] + {c}, others unchanged
      // 1. v'.WF()
      assert v'.WF();
      // 2. Safety(v'): v'.decision == v.decision, so Safety(v') follows from Safety(v)
      assert Safety(v');
      // 3. uniqueness of votes at each node
      assert forall n0, v1, v2 :: v1 in v'.votes[n0] && v2 in v'.votes[n0] ==> v1 == v2;
      // 4. For all c in v'.decision, exists q:Quorum :: ChoiceQuorum(v', q, c)
      forall c | c in v'.decision
        ensures exists q:Quorum :: ChoiceQuorum(v', q, c)
      {
        // v'.decision == v.decision, so c in v.decision
        var q :| ChoiceQuorum(v, q, c);
        // votes only changed at n, and only added c, so ChoiceQuorum(v', q, c) still holds
        assert ChoiceQuorum(v', q, c);
      }
      return;
    }
    case DecideStep(c, q) => {
      // Strongest annotation: v'.decision == v.decision + {c}
      // 1. v'.WF()
      assert v'.WF();
      // 2. Safety(v'): v'.decision = v.decision + {c}, so if v.decision is empty, only c in v'.decision; if not, all elements are equal
      forall c1, c2 | c1 in v'.decision && c2 in v'.decision
        ensures c1 == c2
      {
        if c1 in v.decision && c2 in v.decision {
          assert c1 == c2; // by Inv(v)
        } else if c1 == c && c2 in v.decision {
          // c just added, c2 in v.decision, must be c == c2 by Inv(v) (since c in v.votes[n] for all n in q, and c2 in v.decision)
          var q2 :| ChoiceQuorum(v, q2, c2);
          var n := QuorumIntersect(q, q2);
          assert c in v.votes[n];
          assert c2 in v.votes[n];
          assert c == c2;
        } else if c2 == c && c1 in v.decision {
          var q1 :| ChoiceQuorum(v, q1, c1);
          var n := QuorumIntersect(q1, q);
          assert c1 in v.votes[n];
          assert c in v.votes[n];
          assert c1 == c;
        } else {
          assert c1 == c && c2 == c;
        }
      }
      // 3. uniqueness of votes at each node: votes unchanged
      assert forall n, v1, v2 :: v1 in v'.votes[n] && v2 in v'.votes[n] ==> v1 == v2;
      // 4. For all c0 in v'.decision, exists q0:Quorum :: ChoiceQuorum(v', q0, c0)
      forall c0 | c0 in v'.decision
        ensures exists q0:Quorum :: ChoiceQuorum(v', q0, c0)
      {
        if c0 in v.decision {
          var q0 :| ChoiceQuorum(v, q0, c0);
          assert ChoiceQuorum(v', q0, c0);
        } else {
          // c0 == c
          assert (forall n :: Member(n, q) ==> c in v.votes[n]);
          assert ChoiceQuorum(v', q, c);
        }
      }
      return;
    }
  }
  // END
}

lemma SafetyHolds(v: Variables, v': Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
  if Init(v) {
    InitImpliesInv(v);
  }
  if Inv(v) && Next(v, v') {
    InvInductive(v, v');
  }
  if Inv(v) {
    // Safety(v) is a conjunct of Inv(v)
    assert Safety(v);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
