// Code taken from the following paper: http://leino.science/papers/krml260.pdf

// Each philosopher's pseudocode:

// repeat forever {
//     Thinking:

//     t: Ticket = ticket, ticket + 1 // request ticket to enter hungry state
//     Hungry:
//     //...

//     wait until serving = t; // Enter
//     Eating:
//     //...

//     serving := serving + 1; // Leaving
// }

// control state values; thinking, hungry, eating
// introduce state for each process: use map from processes to values

type Process(==) // {type comes equipped with ability to compare its values with equality}
datatype CState = Thinking | Hungry | Eating

// provides mutual exclusion
class TicketSystem {
    var ticket: int
    var serving: int
    const P: set<Process>

    var cs: map<Process, CState> // cannot use state variable P as domain for maps => use Process => every conceivable process
    var t: map<Process, int> // ticket number for each philosopher

    // how to know some process p is in domain of map: introduce function which tells whether condition holds or not
    predicate Valid() // function which describes system invariant
        reads this // may depend on values in the class
    {
        P <= cs.Keys && P <= t.Keys && serving <= ticket && // ticket may be greater than serving but not the other way around
        (forall p :: p in P && cs[p] != Thinking ==> serving <= t[p] < ticket) && // any current ticket number is in the range of serving to ticket
        (forall p,q :: 
            p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking ==> t[p] != t[q] // some other process may have a value equal to 'serving'
        ) && 
        (forall p :: p in P && cs[p] == Eating ==> t[p] == serving) // if eating, the current ticket number must be the one being served
    }

    constructor (processes: set<Process>)
        ensures Valid() // postcondition
    {
        P := processes;
        ticket := 0;
        serving := 0;
        cs := map p | p in processes :: Thinking; // set initial state of every process to Thinking
        t := map p | p in processes :: 0;

        // Strongest possible annotation after field assignments
        // (no 'assert' allowed before 'new' finishes, so nothing here)
    }

    // atomic events to formalize for each process: request, enter, leave
    // model each atomic event by a method

    method Request(p: Process)
        requires Valid() && p in P && cs[p] == Thinking
        modifies this
        ensures Valid()
    {
        // Before state
        assert cs[p] == Thinking;
        assert serving <= ticket;
        assert forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket;
        assert forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r];
        assert forall q :: q in P && cs[q] == Eating ==> t[q] == serving;

        t := t[p := ticket];
        ticket := ticket + 1;
        cs := cs[p := Hungry];

        // After state
        assert cs[p] == Hungry;
        assert t[p] == ticket - 1;
        assert serving <= ticket;
        assert forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket;
        assert forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r];
        assert forall q :: q in P && cs[q] == Eating ==> t[q] == serving;
        assert Valid();
    }

    method Enter(p: Process)
        requires Valid() && p in P && cs[p] == Hungry
        modifies this
        ensures Valid()
    {
        // Before state
        assert cs[p] == Hungry;
        assert serving <= t[p] < ticket;
        assert forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket;
        assert forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r];
        assert forall q :: q in P && cs[q] == Eating ==> t[q] == serving;

        if t[p] == serving {
            // Only one process can have t[p] == serving and cs[p] == Hungry
            assert forall q :: q in P && q != p && cs[q] != Thinking ==> t[q] != serving;
            cs := cs[p := Eating];

            // After state
            assert cs[p] == Eating;
            assert t[p] == serving;
            assert forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket;
            assert forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r];
            assert forall q :: q in P && cs[q] == Eating ==> t[q] == serving;
        }
        assert Valid();
    }

    method Leave(p: Process)
        requires Valid() && p in P && cs[p] == Eating
        modifies this
        ensures Valid()
    {
        // Before state
        assert cs[p] == Eating;
        assert t[p] == serving;
        assert serving <= ticket;
        assert forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket;
        assert forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r];
        assert forall q :: q in P && cs[q] == Eating ==> t[q] == serving;

        serving := serving + 1;
        cs := cs[p := Thinking];

        // After state
        assert cs[p] == Thinking;
        assert serving <= ticket;
        assert forall q :: q in P && cs[q] != Thinking ==> serving <= t[q] < ticket;
        assert forall q, r :: q in P && r in P && q != r && cs[q] != Thinking && cs[r] != Thinking ==> t[q] != t[r];
        assert forall q :: q in P && cs[q] == Eating ==> t[q] == serving;
        assert Valid();
    }

    // correctness: no two process are in eating state at same time
    // prove that invariant implies condition
    lemma MutualExclusion(p: Process, q: Process)
        requires Valid() && p in P && q in P // if system is in valid state and both p, q are processes
        requires cs[p] == Eating && cs[q] == Eating // both p, q are in Eating state
        ensures p == q // p and q are the same process       
    {
        // By Valid, for any p in P, cs[p] == Eating ==> t[p] == serving
        assert t[p] == serving && t[q] == serving;
        // By Valid, for any p != q, if cs[p] != Thinking && cs[q] != Thinking, then t[p] != t[q]
        if p != q {
            assert cs[p] != Thinking && cs[q] != Thinking;
            assert t[p] != t[q]; // contradiction, since t[p] == t[q] == serving
        }
        // Therefore, p == q
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
