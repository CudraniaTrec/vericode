// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Dafny.
function power(a: int, n: int): int //function for a to the power of n
  requires 0 <= n;

method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0;
/*Post-Condition*/ ensures z==power(x,y0);
{
  var y := y0;  //This is here for Dafny's sake and immutable inputs...
  
  /* (| y=y0 ^ y>=0 |)                          - Pre-Condition */
  /* (| 1=power(x,y0-y) ^ y>=0 |)               - implied (a)   */
  z := 1;
  /* (| z=power(x,y0-y) ^ y>=0 |)               - assignment    */   
  while (y>0)
    invariant 0 <= y <= y0;
    invariant z == power(x, y0 - y);
    invariant y0 >= 0;
  {
    /*   (| z=power(x,y0-y) ^ y>=0 ^ y>0 |)       - partial-while */  
    /*   (| z*x=power(x,y0-(y-1)) ^ (y-1)>=0 |)   - implied (b)   */  
    //assert z == power(x, y0 - y);
    //assert y > 0;
    //assert z * x == power(x, y0 - (y - 1));
    z := z*x;
    /*   (| z=power(x,y0-(y-1)) ^ (y-1)>=0 |)     - assignment    */        
    y := y-1;
    /*   (| z=power(x,y0-y) ^ y>=0 |)             - assignment    */              
    //assert z == power(x, y0 - y);
  }
  /* (| z=power(x,y0-y) ^ y>=0 ^ -(y>0) |)      - partial-while */   
  /* (| z=power(x,y0-y) |)                      - implied (c)   */       
  //assert y == 0;
  //assert z == power(x, y0 - y);
}

function abs(a: real) : real {if a>0.0 then a else -a}
