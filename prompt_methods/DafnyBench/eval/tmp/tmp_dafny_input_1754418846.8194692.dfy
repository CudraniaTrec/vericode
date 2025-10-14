
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
       // Strongest post: v1 == OFF && v2 == ON
       // v3, in_flowv1, in_flowv2, in_flowv3 are uninitialized
   }
  
}
class Tank
{
   var pipe: Pipe;
   var height: int;
    constructor()
    {
        pipe := new Pipe();
        // Strongest post: pipe.v1 == OFF && pipe.v2 == ON
    }
} 

method checkRegulation(tank: Tank)
 //requires tank.pipe.v1==OFF && tank.pipe.v2==ON && (tank.pipe.v3==OFF || tank.pipe.v2==ON) 
ensures (tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2)) 
|| (tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3))
|| ((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1))
modifies tank.pipe;
{
    // Strongest precondition holds:
    assert tank.pipe.v1 == OFF && tank.pipe.v2 == ON && (tank.pipe.v3 == OFF || tank.pipe.v2 == ON);

    if(tank.height >10)
     {
         // Before: tank.pipe.v1 == OFF && tank.pipe.v2 == ON
         tank.pipe.v1:= OFF;
         tank.pipe.v3:= ON;
         // After: tank.pipe.v1 == OFF && tank.pipe.v3 == ON
         assert tank.pipe.v1 == OFF && tank.pipe.v3 == ON;
         assert tank.pipe.v2 == old(tank.pipe.v2);
         // Ensures first disjunct
     }
    else if(tank.height <8)
     {
         // Before: tank.pipe.v1 == OFF && tank.pipe.v2 == ON
         tank.pipe.v1:= OFF;
         tank.pipe.v2:= ON;
         // After: tank.pipe.v1 == OFF && tank.pipe.v2 == ON
         assert tank.pipe.v1 == OFF && tank.pipe.v2 == ON;
         assert tank.pipe.v3 == old(tank.pipe.v3);
         // Ensures second disjunct
     }
     
     // For the third disjunct, we only assume it, as in the code.
     assume(((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1)));
     assert ((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1)) 
         || (tank.height>10 && tank.pipe.v1==OFF && tank.pipe.v3==ON && tank.pipe.v2==old(tank.pipe.v2))
         || (tank.height <8 && tank.pipe.v1== OFF && tank.pipe.v2== ON && tank.pipe.v3==old(tank.pipe.v3));
     /*else if(tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1> 5)
     {

         tank.pipe.v2:= OFF;
         assume(((tank.pipe.in_flowv3 >5 || tank.pipe.in_flowv1 >5 ) && tank.pipe.v2==OFF && tank.pipe.v3==old(tank.pipe.v3) && tank.pipe.v1==old(tank.pipe.v1)));
     } */
     
} 

function abs(a: real) : real {if a>0.0 then a else -a}
