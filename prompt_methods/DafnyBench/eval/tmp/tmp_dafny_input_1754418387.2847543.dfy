
// Model a lock service that consists of a single server and an
// arbitrary number of clients.
//
// The state of the system includes the server's state (whether the server
// knows that some client holds the lock, and if so which one)
// and the clients' states (for each client, whether that client knows
// it holds the lock).
//
// The system should begin with the server holding the lock.
// An acquire step atomically transfers the lock from the server to some client.
// (Note that we're not modeling the network yet -- the lock disappears from
// the server and appears at a client in a single atomic transition.)
// A release step atomically transfers the lock from the client back to the server.
//
// The safety property is that no two clients ever hold the lock
// simultaneously.

// SOLUTION
datatype ServerGrant = Unlocked | Client(id: nat)
datatype ClientRecord = Released | Acquired
datatype Variables = Variables(
  clientCount: nat, /* constant */
  server: ServerGrant, clients: seq<ClientRecord>
) {
  ghost predicate ValidIdx(idx: int) {
    0 <= idx < this.clientCount
  }
  ghost predicate WellFormed() {
    |clients| == this.clientCount
  }
}
// END


ghost predicate Init(v:Variables) {
  && v.WellFormed()
     // SOLUTION
  && v.server.Unlocked?
  && |v.clients| == v.clientCount
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
     // END
}
// SOLUTION
ghost predicate Acquire(v:Variables, v':Variables, id:int) {
  && v.WellFormed()
  && v'.WellFormed()
  && v.ValidIdx(id)

  && v.server.Unlocked?

  && v'.server == Client(id)
  && v'.clients == v.clients[id := Acquired]
  && v'.clientCount == v.clientCount
}

ghost predicate Release(v:Variables, v':Variables, id:int) {
  && v.WellFormed()
  && v'.WellFormed()
  && v.ValidIdx(id)

  && v.clients[id].Acquired?

  && v'.server.Unlocked?
  && v'.clients == v.clients[id := Released]
  && v'.clientCount == v.clientCount
}
// END
// Jay-Normal-Form: pack all the nondeterminism into a single object
// that gets there-exist-ed once.
datatype Step =
    // SOLUTION
  | AcquireStep(id: int)
  | ReleaseStep(id: int)
    // END

ghost predicate NextStep(v:Variables, v':Variables, step: Step) {
  match step
  // SOLUTION
  case AcquireStep(id) => Acquire(v, v', id)
  case ReleaseStep(id) => Release(v, v', id)
  // END
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{
  // No code needed; proof is trivial by definition.
}

ghost predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

// A good definition of safety for the lock server is that no two clients
// may hold the lock simultaneously. This predicate should capture that
// idea in terms of the Variables you have defined.
ghost predicate Safety(v:Variables) {
  // SOLUTION
  forall i,j |
    0 <= i < |v.clients| &&
    0 <= j < |v.clients| &&
    v.clients[i].Acquired? &&
    v.clients[j].Acquired?
    :: i == j
  // END
}


// This predicate should be true if and only if the client with index `clientIndex`
// has the lock acquired.
// Since you defined the Variables state, you must define this predicate in
// those terms.
ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{
  // SOLUTION
  v.server == Client(clientIndex)
  // END
}

// Show a behavior that the system can release a lock from clientA and deliver
// it to clientB.
lemma PseudoLiveness(clientA:nat, clientB:nat) returns (behavior:seq<Variables>)
  requires clientA == 2
  requires clientB == 0
  ensures 2 <= |behavior|  // precondition for index operators below
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior|-1 :: Next(behavior[i], behavior[i+1]) // Behavior satisfies your state machine
  ensures forall i | 0 <= i < |behavior| :: Safety(behavior[i]) // Behavior always satisfies the Safety predicate
  ensures behavior[|behavior|-1].WellFormed() // precondition for calling ClientHoldsLock
  ensures ClientHoldsLock(behavior[1], clientA) // first clientA acquires lock
  ensures ClientHoldsLock(behavior[|behavior|-1], clientB) // eventually clientB acquires lock
{
  // SOLUTION
  // All indices and states must be well-formed and satisfy preconditions.

  // The initial state must have the server Unlocked, all clients Released.
  var state0 := Variables(clientCount := 3, server := Unlocked, clients := [Released, Released, Released]);
  // After clientA acquires, server gives lock to clientA, only clientA is Acquired.
  var state1 := Variables(clientCount := 3, server := Client(clientA), clients := [Released, Released, Acquired]);
  // After clientA releases, server is Unlocked, all clients Released.
  var state2 := Variables(clientCount := 3, server := Unlocked, clients := [Released, Released, Released]);
  // After clientB acquires, server gives lock to clientB, only clientB is Acquired.
  var state3 := Variables(clientCount := 3, server := Client(clientB), clients := [Acquired, Released, Released]);
  behavior := [state0, state1, state2, state3];

  // Strongest possible annotations:
  assert state0.WellFormed();
  assert state1.WellFormed();
  assert state2.WellFormed();
  assert state3.WellFormed();

  assert Init(state0);

  // Step 0 -> 1: Acquire by clientA
  assert Acquire(state0, state1, clientA);
  assert NextStep(state0, state1, AcquireStep(clientA));
  assert Next(state0, state1);

  // Step 1 -> 2: Release by clientA
  assert Release(state1, state2, clientA);
  assert NextStep(state1, state2, ReleaseStep(clientA));
  assert Next(state1, state2);

  // Step 2 -> 3: Acquire by clientB
  assert Acquire(state2, state3, clientB);
  assert NextStep(state2, state3, AcquireStep(clientB));
  assert Next(state2, state3);

  // Safety at each step
  assert Safety(state0);
  assert Safety(state1);
  assert Safety(state2);
  assert Safety(state3);

  // ClientHoldsLock assertions
  assert ClientHoldsLock(state1, clientA);
  assert ClientHoldsLock(state3, clientB);

  // END
}

function abs(a: real) : real {if a>0.0 then a else -a}
