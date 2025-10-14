
/*
  A simple state machine modeling checking out and returning books in a library.
*/

// Status will track where one book is
datatype Status = Shelf | Patron(name: string)
datatype Book = Book(title: string)

// The state of the whole library is just the status of every book owned by the
// library.
datatype Variables = Variables(library: map<Book, Status>)
{
  // New syntax (member function): the curly braces below the datatype introduce
  // a set of _member functions_, which can be called as v.f(), just like Java,
  // C++, or Rust methods. Just like in Java or C++, the body can use the `this`
  // keyword to refer to an implicit argument of type Variables.
  ghost predicate WellFormed()
  {
    // New syntax (x in m for maps): maps have a domain and we can write x in m
    // to say x is in the domain of m (similarly, `x !in m` is a more readable
    // version of `!(x in m)`). As with sequences where indices need to be in
    // bounds, to write `m[x]` you'll need to show that `x in m` holds.
    //
    // What we're saying here is that the empty-titled book is not owned by the
    // library.
    forall b: Book :: b.title == "" ==> b !in this.library
  }
}

ghost predicate Init(v: Variables)
{
  && v.WellFormed()
  && forall b :: b in v.library ==> v.library[b].Shelf?
}

// The transitions of the library state machine.

datatype Step = Checkout(b: Book, to: string) | Return(b: Book)

ghost predicate CheckoutStep(v: Variables, v': Variables, step: Step)
  requires step.Checkout?
{
  && v.WellFormed()
  && step.b in v.library
  && v.library[step.b].Shelf?
     // New syntax (datatype update): here we define the new Variables from the old
     // one by updating one field: v.(library := ...). This is much like a sequence
     // update. In fact, we also introduce a map update `v.library[step.b := ...]`
     // which works in pretty much the same way.
  && v' == v.(library := v.library[step.b := Patron(step.to)])
}

ghost predicate ReturnStep(v: Variables, v': Variables, step: Step)
  requires step.Return?
{
  && v.WellFormed()
  && step.b in v.library
  && v.library[step.b].Patron?
  && v' == v.(library := v.library[step.b := Shelf])
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case Checkout(_, _) => CheckoutStep(v, v', step)
    case Return(_) => ReturnStep(v, v', step)
  }
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{
  // Strongest proof: by case analysis on step
  match step {
    case Checkout(b, to) =>
      // By definition, v' == v.(library := v.library[b := Patron(to)])
      // Any v'' with NextStep(v, v'', step) must also be v.(library := v.library[b := Patron(to)])
      // So v' == v''
      assert CheckoutStep(v, v', step);
      forall v'' | NextStep(v, v'', step)
        ensures v' == v''
      {
        assert CheckoutStep(v, v'', step);
        assert v' == v.(library := v.library[b := Patron(to)]);
        assert v'' == v.(library := v.library[b := Patron(to)]);
        assert v' == v'';
      }
    case Return(b) =>
      assert ReturnStep(v, v', step);
      forall v'' | NextStep(v, v'', step)
        ensures v' == v''
      {
        assert ReturnStep(v, v'', step);
        assert v' == v.(library := v.library[b := Shelf]);
        assert v'' == v.(library := v.library[b := Shelf]);
        assert v' == v'';
      }
  }
}

/*
In this lemma we'll write a concrete sequence of states which forms a (short)
execution of this state machine, and prove that it really is an execution.

This can be a good sanity check on the definitions (for example, to make sure
that it's at least possible to take every transition).
*/
lemma ExampleExec() {
  var e := [
    Variables(library := map[Book("Snow Crash") := Shelf, Book("The Stand") := Shelf]),
    Variables(library := map[Book("Snow Crash") := Patron("Jon"), Book("The Stand") := Shelf]),
    Variables(library := map[Book("Snow Crash") := Patron("Jon"), Book("The Stand") := Patron("Tej")]),
    Variables(library := map[Book("Snow Crash") := Shelf, Book("The Stand") := Patron("Tej")])
  ];

  // Next we'll prove that e is a valid execution.

  // These steps will be witnesses to help prove Next between every pair of Variables.
  var steps := [
    Checkout(Book("Snow Crash"), "Jon"),
    Checkout(Book("The Stand"), "Tej"),
    Return(Book("Snow Crash"))
  ];

  // Strongest possible annotations:
  // Prove initial state is well-formed and Init
  assert e[0].WellFormed();
  assert Init(e[0]);

  // Prove each step is a valid NextStep and thus Next
  // Step 0: e[0] --steps[0]--> e[1]
  assert steps[0].Checkout?;
  assert Book("Snow Crash") in e[0].library;
  assert e[0].library[Book("Snow Crash")].Shelf?;
  assert CheckoutStep(e[0], e[1], steps[0]);
  assert NextStep(e[0], e[1], steps[0]);
  assert Next(e[0], e[1]);

  // Step 1: e[1] --steps[1]--> e[2]
  assert steps[1].Checkout?;
  assert Book("The Stand") in e[1].library;
  assert e[1].library[Book("The Stand")].Shelf?;
  assert CheckoutStep(e[1], e[2], steps[1]);
  assert NextStep(e[1], e[2], steps[1]);
  assert Next(e[1], e[2]);

  // Step 2: e[2] --steps[2]--> e[3]
  assert steps[2].Return?;
  assert Book("Snow Crash") in e[2].library;
  assert e[2].library[Book("Snow Crash")].Patron?;
  assert ReturnStep(e[2], e[3], steps[2]);
  assert NextStep(e[2], e[3], steps[2]);
  assert Next(e[2], e[3]);

  // Prove all states are well-formed
  forall i | 0 <= i < |e| :: e[i].WellFormed();

  // Prove all transitions are valid
  forall i | 0 <= i < |steps| ::
    NextStep(e[i], e[i+1], steps[i]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
