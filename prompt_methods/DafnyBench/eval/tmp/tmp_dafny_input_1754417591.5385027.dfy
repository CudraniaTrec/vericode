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
  ghost predicate WellFormed()
  {
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
  if step.Checkout? then
    CheckoutStep(v, v', step)
  else
    ReturnStep(v, v', step)
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

lemma NextStepDeterministicGivenStep(v:Variables, v':Variables, step: Step)
  requires NextStep(v, v', step)
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
{
  if step.Checkout? {
    // NextStep(v, v', step) <==> CheckoutStep(v, v', step)
    // So v' == v.(library := v.library[step.b := Patron(step.to)])
    forall v'' | NextStep(v, v'', step)
      ensures v' == v''
    {
      assert CheckoutStep(v, v'', step);
      assert v' == v.(library := v.library[step.b := Patron(step.to)]);
      assert v'' == v.(library := v.library[step.b := Patron(step.to)]);
      assert v' == v'';
    }
  } else {
    // step.Return?
    forall v'' | NextStep(v, v'', step)
      ensures v' == v''
    {
      assert ReturnStep(v, v'', step);
      assert v' == v.(library := v.library[step.b := Shelf]);
      assert v'' == v.(library := v.library[step.b := Shelf]);
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

  // e[0] is a valid initial state
  assert e[0].WellFormed();
  assert forall b :: b in e[0].library ==> e[0].library[b].Shelf?;
  assert Init(e[0]);

  // Step 0: e[0] --steps[0]--> e[1]
  assert steps[0].Checkout?;
  assert steps[0].b == Book("Snow Crash");
  assert steps[0].to == "Jon";
  assert e[0].WellFormed();
  assert Book("Snow Crash") in e[0].library;
  assert e[0].library[Book("Snow Crash")].Shelf?;
  assert e[1] == e[0].(library := e[0].library[Book("Snow Crash") := Patron("Jon")]);
  assert CheckoutStep(e[0], e[1], steps[0]);
  assert NextStep(e[0], e[1], steps[0]);
  assert Next(e[0], e[1]);

  // Step 1: e[1] --steps[1]--> e[2]
  assert steps[1].Checkout?;
  assert steps[1].b == Book("The Stand");
  assert steps[1].to == "Tej";
  assert e[1].WellFormed();
  assert Book("The Stand") in e[1].library;
  assert e[1].library[Book("The Stand")].Shelf?;
  assert e[2] == e[1].(library := e[1].library[Book("The Stand") := Patron("Tej")]);
  assert CheckoutStep(e[1], e[2], steps[1]);
  assert NextStep(e[1], e[2], steps[1]);
  assert Next(e[1], e[2]);

  // Step 2: e[2] --steps[2]--> e[3]
  assert steps[2].Return?;
  assert steps[2].b == Book("Snow Crash");
  assert e[2].WellFormed();
  assert Book("Snow Crash") in e[2].library;
  assert e[2].library[Book("Snow Crash")].Patron?;
  assert e[3] == e[2].(library := e[2].library[Book("Snow Crash") := Shelf]);
  assert ReturnStep(e[2], e[3], steps[2]);
  assert NextStep(e[2], e[3], steps[2]);
  assert Next(e[2], e[3]);

  // The full execution is valid: for all i < |e|-1, Next(e[i], e[i+1])
  forall i | 0 <= i < |e| - 1
    ensures Next(e[i], e[i+1])
  {
    if i == 0 {
      assert Next(e[0], e[1]);
    } else if i == 1 {
      assert Next(e[1], e[2]);
    } else if i == 2 {
      assert Next(e[2], e[3]);
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
