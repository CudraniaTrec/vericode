
module OneSpec {
    datatype Variables = Variables(value: int)

    predicate Init(v: Variables)
    {
        v.value == 0
    }

    predicate IncrementOp(v: Variables, v': Variables)
    {
        && v'.value == v.value + 1
    }

    predicate DecrementOp(v: Variables, v': Variables)
    {
        && v'.value == v.value - 1
    }

    datatype Step = 
        | IncrementStep()
        | DecrementStep()

    predicate NextStep(v: Variables, v': Variables, step: Step)
    {
        match step
            case IncrementStep() => IncrementOp(v, v')
            case DecrementStep() => DecrementOp(v, v')
    }

    predicate Next(v: Variables, v': Variables)
    {
        exists step :: NextStep(v, v', step)
    }
}

module OneProtocol {
    datatype Variables = Variables(value: int)

    predicate Init(v: Variables)
    {
        v.value == 0
    }

    predicate IncrementOp(v: Variables, v': Variables)
    {
        && v'.value == v.value - 1
    }

    predicate DecrementOp(v: Variables, v': Variables)
    {
        && v'.value == v.value + 1
    }

    datatype Step = 
        | IncrementStep()
        | DecrementStep()

    predicate NextStep(v: Variables, v': Variables, step: Step)
    {
        match step 
            case IncrementStep() => IncrementOp(v, v')
            case DecrementStep() => DecrementOp(v, v')
    }

    predicate Next(v: Variables, v': Variables)
    {
        exists step :: NextStep(v, v', step)
    }
}

module RefinementProof {
    import OneSpec
    import opened OneProtocol

    function Abstraction(v: Variables) : OneSpec.Variables {
        OneSpec.Variables(v.value)
    }

    lemma RefinementInit(v: Variables)
        requires Init(v)
        ensures OneSpec.Init(Abstraction(v))
    {
        // strongest annotation: v.value == 0
        assert v.value == 0;
        // Abstraction(v).value == v.value == 0
        assert Abstraction(v).value == 0;
        // OneSpec.Init(Abstraction(v)) == Abstraction(v).value == 0
    }

    lemma RefinementNext(v: Variables, v': Variables)
        requires Next(v, v')
        ensures OneSpec.Next(Abstraction(v), Abstraction(v'))
    {
        var step :| NextStep(v, v', step);
        // strongest annotation: NextStep(v, v', step)
        assert NextStep(v, v', step);
        match step {
            case IncrementStep() => {
                // IncrementOp(v, v') holds, i.e., v'.value == v.value - 1
                assert v'.value == v.value - 1;
                // Abstraction(v').value == v'.value == v.value - 1 == Abstraction(v).value - 1
                assert Abstraction(v').value == Abstraction(v).value - 1;
                // OneSpec.DecrementOp(Abstraction(v), Abstraction(v')) holds
                assert OneSpec.DecrementOp(Abstraction(v), Abstraction(v'));
                // OneSpec.NextStep(Abstraction(v), Abstraction(v'), OneSpec.DecrementStep())
                assert OneSpec.NextStep(Abstraction(v), Abstraction(v'), OneSpec.DecrementStep());
            }
            case DecrementStep() => {
                // DecrementOp(v, v') holds, i.e., v'.value == v.value + 1
                assert v'.value == v.value + 1;
                // Abstraction(v').value == v'.value == v.value + 1 == Abstraction(v).value + 1
                assert Abstraction(v').value == Abstraction(v).value + 1;
                // OneSpec.IncrementOp(Abstraction(v), Abstraction(v')) holds
                assert OneSpec.IncrementOp(Abstraction(v), Abstraction(v'));
                // OneSpec.NextStep(Abstraction(v), Abstraction(v'), OneSpec.IncrementStep())
                assert OneSpec.NextStep(Abstraction(v), Abstraction(v'), OneSpec.IncrementStep());
            }
        }
        // OneSpec.Next(Abstraction(v), Abstraction(v')) holds because there exists a step
        assert OneSpec.Next(Abstraction(v), Abstraction(v'));
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
