datatype Valve = ON | OFF

class Pipe{
   var v1: Valve; //outlet valve 
   var v2: Valve; //inlet Valve
   var v3: Valve; //outlet valve
   var in_flowv1: int; //flow in valve v1
   var in_flowv2: int; //flow in vave v2
   var in_flowv3: int; //flow in valve v3

   constructor()
   {
       this.v1:= OFF;
       this.v2:= ON;
   }
  
}
class Tank
{
   var pipe: Pipe;
   var height: int;
    constructor()
    {
        pipe := new Pipe();
    }
} 

method checkRegulation(tank: Tank)
 //requires tank.pipe.v1==OFF && tank.pipe.v2==ON && (tank.pipe.v3==OFF || tank.pipe.v2==ON) 
ensures (tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2)) 
|| (tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3))
|| ((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1))
modifies tank.pipe;
{
    var old_v1 := tank.pipe.v1;
    var old_v2 := tank.pipe.v2;
    var old_v3 := tank.pipe.v3;

    if(tank.height >10)
     {
         tank.pipe.v1:= OFF;
         tank.pipe.v3:= ON;
         // assert for postcondition
         assert tank.pipe.v1 == OFF;
         assert tank.pipe.v3 == ON;
         assert tank.pipe.v2 == old_v2;
         // Ensures first disjunct
     }
    else if(tank.height <8)
     {
         tank.pipe.v1:= OFF;
         tank.pipe.v2:= ON;
         // assert for postcondition
         assert tank.pipe.v1 == OFF;
         assert tank.pipe.v2 == ON;
         assert tank.pipe.v3 == old_v3;
         // Ensures second disjunct
     }
    else if (tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5)
    {
         tank.pipe.v2 := OFF;
         // assert for postcondition
         assert (tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5);
         assert tank.pipe.v2 == OFF;
         assert tank.pipe.v3 == old_v3;
         assert tank.pipe.v1 == old_v1;
         // Ensures third disjunct
    }
    // No other cases possible due to precondition and postcondition structure
} 

function abs(a: real) : real {if a>0.0 then a else -a}
