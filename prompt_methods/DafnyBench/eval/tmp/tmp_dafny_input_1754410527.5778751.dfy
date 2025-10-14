class Counter {
 
  var value : int ;
  
  constructor init() 
  ensures value == 0;
  {
    value := 0 ;
  }
  
  method getValue() returns (x:int)
  ensures x == value;
  {
    x := value ;
    assert x == value;
  }
  
  method inc()
  modifies this`value
  requires value >= 0;
  ensures value == old(value) + 1; 
  {
    assert value >= 0;
    value := value + 1;
    assert value == old(value) + 1;
    assert value > 0;
  }
  
  method dec()
  modifies this`value
  requires value > 0;
  ensures value == old(value) - 1; 
  {  
    assert value > 0;
    value := value - 1 ;
    assert value == old(value) - 1;
    assert value >= 0;
  }
  
  method Main ()
  {
   var count := new Counter.init() ;
   count.inc();
   count.inc();
   count.dec();
   count.inc();
   var aux : int := count.getValue();
   assert aux == count.value;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
