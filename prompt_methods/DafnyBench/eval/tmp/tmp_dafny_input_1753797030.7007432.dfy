
/*
 * Model of the ticket system and correctness theorem
 * Parts 4 and 5 in the paper
 */
type Process(==) = int  // Philosopher

datatype CState = Thinking | Hungry | Eating  // Control states

// A class can have state, with multiple fields, methods, a constructor, and declare functions and lemmas
class TicketSystem
{
  var ticket: int  // Ticket dispenser
  var serving: int  // Serving display

  const P: set<Process>  // Fixed set of processes

  // State for each process
  var cs: map<Process, CState>  // (Partial) Map from process to state
  var t: map<Process, int>  // (Partial) Map from process to ticket number

  // Invariant of the system
  // Checks that P is a subset of the domain/keys of each map
  predicate Valid()
    reads this  // Depends on the fields on the current class
  {
    && cs.Keys == t.Keys == P  // Alt. P <= cs.Keys && P <= t.Keys
    && serving <= ticket
    && (forall p ::  // ticket help is in range(serving, ticket)
      p in P && cs[p] != Thinking
      ==> serving <= t[p] < ticket
    )
    && (forall p, q ::  // No other process can have the ticket number equals to serving
      p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking
      ==> t[p] != t[q]
    )
    && (forall p ::  // We are serving the correct ticket number
      p in P && cs[p] == Eating
      ==> t[p] == serving
    )
  }

  // Initialize the ticket system
  constructor (processes: set<Process>)
    ensures Valid()  // Postcondition
    ensures P == processes  // Connection between processes and ts.P
  {
    P := processes;
    ticket, serving := 0, 0;  // Alt. ticket := serving;
    // The two following use map comprehension
    cs := map p | p in processes :: Thinking;  // The map from p, where p in processes, takes value Thinking
    t := map p | p in processes :: 0;
    assert cs.Keys == processes;
    assert t.Keys == processes;
    assert serving == 0 && ticket == 0;
    assert (forall p :: p in P && cs[p] != Thinking ==> serving <= t[p] < ticket);
    assert (forall p, q :: p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking ==> t[p] != t[q]);
    assert (forall p :: p in P && cs[p] == Eating ==> t[p] == serving);
  }

  // The next three methods are our atomic events
  // A Philosopher is Thinking and gets Hungry
  method Request(p: Process)
    requires Valid() && p in P && cs[p] == Thinking  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures Valid()  // Postcondition
  {
    t, ticket := t[p := ticket], ticket + 1;  // Philosopher gets current ticket, next ticket's number increases
    cs := cs[p := Hungry];  // Philosopher's state changes to Hungry
    assert cs.Keys == t.Keys == P;
    assert serving <= ticket;
    assert (forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket);
    assert (forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r]);
    assert (forall q :: q in P && cs[q] == Eating ==> t[q] == serving);
  }

  // A Philosopher is Hungry and enters the kitchen
  method Enter(p: Process)
    requires Valid() && p in P && cs[p] == Hungry  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures Valid()  // Postcondition
  {
    if t[p] == serving  // The kitchen is available for this Philosopher
    {
      cs := cs[p := Eating];  // Philosopher's state changes to Eating
      assert cs.Keys == t.Keys == P;
      assert serving <= ticket;
      assert (forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket);
      assert (forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r]);
      assert (forall q :: q in P && cs[q] == Eating ==> t[q] == serving);
    }
  }

  // A Philosopher is done Eating and leaves the kitchen
  method Leave(p: Process)
    requires Valid() && p in P && cs[p] == Eating  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures Valid()  // Postcondition
  {
    assert t[p] == serving;  // Ticket held by p is equal to serving
    serving := serving + 1;  // Kitchen is ready to serve the next ticket holder
    cs := cs[p := Thinking];  // Philosopher's state changes to Thinking
    assert cs.Keys == t.Keys == P;
    assert serving <= ticket;
    assert (forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket);
    assert (forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r]);
    assert (forall q :: q in P && cs[q] == Eating ==> t[q] == serving);
  }

  // Ensures that no two processes are in the same state
  lemma MutualExclusion(p: Process, q: Process)
    // Antecedents
    requires Valid() && p in P && q in P
    requires cs[p] == Eating && cs[q] == Eating
    // Conclusion/Proof goal
    ensures p == q
  {
    assert t[p] == serving;
    assert t[q] == serving;
    if p != q {
      assert cs[p] != Thinking && cs[q] != Thinking;
      assert t[p] != t[q];
      assert false;
    }
  }
}

/*
 * Event scheduler
 * Part 6 in the paper
 * Part 6.1 for alternatives
 */
method Run(processes: set<Process>)
  requires processes != {}  // Cannot schedule no processes
{
  var ts := new TicketSystem(processes);
  var schedule := [];  // Scheduling choices
  var trace := [(ts.ticket, ts.serving, ts.cs, ts.t)];  // Record sequence of states
  
  while true
    invariant ts.Valid()
    invariant ts.P == processes
    invariant ts.cs.Keys == processes
    invariant ts.t.Keys == processes
    invariant ts.serving <= ts.ticket
    invariant (forall p :: p in processes && ts.cs[p] != Thinking ==> ts.serving <= ts.t[p] < ts.ticket)
    invariant (forall p, q :: p in processes && q in processes && p != q && ts.cs[p] != Thinking && ts.cs[q] != Thinking ==> ts.t[p] != ts.t[q])
    invariant (forall p :: p in processes && ts.cs[p] == Eating ==> ts.t[p] == ts.serving)
    invariant |schedule| == |trace| - 1
  {
    var p :| p in ts.P;  // p exists such that p is in ts.P
    match ts.cs[p] {
      case Thinking => ts.Request(p);
      case Hungry => ts.Enter(p);
      case Eating => ts.Leave(p);
    }
    schedule := schedule + [p];
    trace:=trace + [(ts.ticket, ts.serving, ts.cs, ts.t)];
  }
}

/*
 * Event scheduler with planified schedule
 * Part 6.2
 */
method RunFromSchedule(processes: set<Process>, schedule: nat -> Process)
  requires processes != {}
  requires forall n :: schedule(n) in processes
{
  var ts := new TicketSystem(processes);
  var n := 0;
  
  while true
    invariant ts.Valid()
    invariant ts.P == processes
    invariant ts.cs.Keys == processes
    invariant ts.t.Keys == processes
    invariant ts.serving <= ts.ticket
    invariant (forall p :: p in processes && ts.cs[p] != Thinking ==> ts.serving <= ts.t[p] < ts.ticket)
    invariant (forall p, q :: p in processes && q in processes && p != q && ts.cs[p] != Thinking && ts.cs[q] != Thinking ==> ts.t[p] != ts.t[q])
    invariant (forall p :: p in processes && ts.cs[p] == Eating ==> ts.t[p] == ts.serving)
    invariant n >= 0
  {
    var p := schedule(n);
    match ts.cs[p] {
      case Thinking => ts.Request(p);
      case Hungry => ts.Enter(p);
      case Eating => ts.Leave(p);
    }
    n := n + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
