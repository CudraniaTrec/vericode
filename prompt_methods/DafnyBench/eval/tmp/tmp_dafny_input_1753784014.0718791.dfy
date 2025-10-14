
// A8Q2 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

method A8Q1(x: int, y: int, z: int) returns (m: int)
/*Pre-Condition*/   requires true;
/*Post-Condition*/  ensures m<=x && m<=y && m<=z;
{ 
  /* (| true |)                               - Pre-Condition */
      if(z<y){
      /* (| z<y |)                            - if-then-else  */   
          if(z<x){
            /* (| z<y ^ z<=x |)               - if-then-else  */  
            assert z < y;
            assert z < x;
            assert z <= x;
            assert z <= y;
            assert z <= z;
            /* (| z<=x ^ z<=y ^ z<=z |)       - implied (a)   */  
                m := z;
            assert m == z;
            assert m <= x && m <= y && m <= z;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }else{
            /* (| z<y ^ -(z<=x) |)            - if-then-else  */  
            assert z < y;
            assert !(z < x);
            assert x <= z;
            assert x <= x;
            assert x <= y;
            assert x <= z;
            /* (| x<=x ^ x<=y ^ x<=z |)       - implied (b)   */  
                m := x;
            assert m == x;
            assert m <= x && m <= y && m <= z;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }
      }else{
      /* (| -(z<y) |)                         - if-then-else  */  
      assert !(z < y);
      assert y <= z;
      assert y <= y;
      assert y <= z;
      /* (| y<=y ^ y<=z |)                    - implied (c)   */  
          m := y;
      assert m == y;
      assert m <= y && m <= z;
      /* (| m<=y ^ y<=z |)                    - assignment    */  
          if (x<y){
            /* (| m<=y ^ y<=z ^ x<y |)        - if-then       */  
            assert x < y;
            assert x <= x;
            assert x <= y;
            assert x <= z;
            /* (| x<=x ^ x<=y ^ x<=z |)       - implied (d)   */  
                m := x;
            assert m == x;
            assert m <= x && m <= y && m <= z;
            /* (| m<=x ^ m<=y ^ m<=z |)       - assignment    */  
          }
      assert m <= x && m <= y && m <= z;
      /* (| m<=x ^ m<=y ^ m<=z |)             - if-then: implied (e) */  
      }
  assert m <= x && m <= y && m <= z;
  /* (| m<=x ^ m<=y ^ m<=z |)                 - if-then-else  */  
}

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/

function abs(a: real) : real {if a>0.0 then a else -a}
