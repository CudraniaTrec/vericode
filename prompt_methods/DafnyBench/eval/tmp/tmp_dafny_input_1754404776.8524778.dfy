class Grinder { 
	ghost var hasBeans: bool 
    ghost var Repr: set<object>

	ghost predicate Valid() 
		reads this, Repr
        ensures Valid() ==> this in Repr
	{
		this in Repr &&
		Repr != {}
	}
		
	constructor() 
		ensures Valid() && fresh(Repr) && !hasBeans
	{
		hasBeans := false;
		Repr := {this};
		assert Valid();
	}

    function Ready(): bool 
		requires Valid() 
		reads Repr
		ensures Ready() == hasBeans 
	{
		hasBeans
	}

	method AddBeans() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && hasBeans && fresh(Repr-old(Repr))
	{
		hasBeans := true;
		var oldRepr := Repr;
		Repr := Repr + {new object};
		assert fresh(Repr - oldRepr);
		assert Valid();
		assert hasBeans;
	}

	method Grind() 
		requires Valid() && hasBeans 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr))
	{
		hasBeans := false;
		var oldRepr := Repr;
		Repr := Repr + {new object};
		assert fresh(Repr - oldRepr);
		assert Valid();
	}
}

class WaterTank { 
	ghost var waterLevel: nat
    ghost var Repr: set<object>

	ghost predicate Valid() 			 
		reads this, Repr 		
        ensures Valid() ==> this in Repr
	{
		this in Repr &&
		waterLevel >= 0 &&
		Repr != {}
	}

	constructor() 				 
		ensures Valid() && fresh(Repr) && waterLevel == 0
	{
		waterLevel := 0;
		Repr := {this};
		assert Valid();
		assert waterLevel == 0;
	}

    function Level(): nat 
		requires Valid()
		reads Repr
		ensures Level() == waterLevel
	{
		waterLevel
	}

	method Fill() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr)) && waterLevel == 10 
	{
		waterLevel := 10;
		var oldRepr := Repr;
		Repr := Repr + {new object};
		assert fresh(Repr - oldRepr);
		assert waterLevel == 10;
		assert Valid();
	}

	method Use() 
		requires Valid() && waterLevel != 0 
		modifies Repr 
		ensures Valid() && fresh(Repr-old(Repr)) && waterLevel == old(Level()) - 1  
	{
		var oldLevel := waterLevel;
		waterLevel := waterLevel - 1;
		var oldRepr := Repr;
		Repr := Repr + {new object};
		assert fresh(Repr - oldRepr);
		assert waterLevel == oldLevel - 1;
		assert Valid();
	}
}

class CoffeeMaker { 	
	var g: Grinder 	
	var w: WaterTank
	ghost var ready: bool
	ghost var Repr: set<object>

	ghost predicate Valid() 
		reads this, Repr 
        ensures Valid() ==> this in Repr
	{ 
		this in Repr && g in Repr && w in Repr &&
		g.Repr <= Repr && w.Repr <= Repr &&
		g.Valid() && w.Valid() &&
		this !in g.Repr && this !in w.Repr && w.Repr !! g.Repr &&
		ready == (g.hasBeans && w.waterLevel != 0) 
	}

    constructor() 
		ensures Valid() && fresh(Repr)
	{ 
		g := new Grinder;
		w := new WaterTank;
		ready := false;
		Repr := {this, g, w} + g.Repr + w.Repr;
		assert g.Valid();
		assert w.Valid();
		assert Valid();
	}

    predicate Ready() 
		requires Valid() 
		reads Repr
		ensures Ready() == ready
	{ 
		g.Ready() && w.Level() != 0
	}

    method Restock() 
		requires Valid() 
		modifies Repr 
		ensures Valid() && Ready() && fresh(Repr - old(Repr))
	{ 
		var oldRepr := Repr;
		g.AddBeans(); 
		w.Fill();  
		ready := true;
		Repr := {this, g, w} + g.Repr + w.Repr;
		assert g.hasBeans;
		assert w.waterLevel == 10;
		assert ready == (g.hasBeans && w.waterLevel != 0);
		assert Valid();
		assert Ready();
		assert fresh(Repr - oldRepr);
	} 

    method Dispense()
		requires Valid() && Ready() 
		modifies Repr 
		ensures Valid() && fresh(Repr - old(Repr))
	{ 	
		var oldRepr := Repr;
		g.Grind(); 
		w.Use(); 
		ready := g.hasBeans && w.waterLevel != 0;
		Repr := {this, g, w} + g.Repr + w.Repr;
		assert ready == (g.hasBeans && w.waterLevel != 0);
		assert Valid();
		assert fresh(Repr - oldRepr);
	}
}

method CoffeeTestHarness() { 
	var cm := new CoffeeMaker;
	cm.Restock(); 
	cm.Dispense();
}

function abs(a: real) : real {if a>0.0 then a else -a}
