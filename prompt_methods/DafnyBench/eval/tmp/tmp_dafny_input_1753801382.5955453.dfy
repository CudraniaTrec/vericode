
function eight(x: nat):nat {
    9 * x + 5
}

predicate isOdd(x: nat) {
    x % 2 == 1
}

predicate isEven(x: nat) {
    x % 2 == 0
}

lemma eightL(x: nat)
    requires isOdd(x)
    ensures isEven(eight(x))
{
    // 9*x is odd when x is odd, 9*odd = odd
    // odd + 5 = even (since odd+odd=even)
    // So, eight(x) = odd + odd = even
    assert x % 2 == 1;
    assert (9 * x) % 2 == 1;
    assert (9 * x + 5) % 2 == (1 + 1) % 2;
    assert (9 * x + 5) % 2 == 0;
    assert isEven(eight(x));
}

function nineteenf(x: nat): nat {
    7*x+4
}
function nineteens(x: nat): nat {
    3*x+11
}

lemma nineteenlemma(x: nat) 
    requires isEven(nineteenf(x))
    ensures isOdd(nineteens(x))
{
    // nineteenf(x) = 7x + 4 even => 7x even
    // 7x even <=> x even
    // So x even
    assert nineteenf(x) % 2 == 0;
    assert (7 * x + 4) % 2 == 0;
    assert (7 * x) % 2 == 0;
    assert x % 2 == 0;
    // nineteens(x) = 3x + 11, x even => 3x even, even + odd = odd
    assert (3 * x) % 2 == 0;
    assert (3 * x + 11) % 2 == (0 + 1) % 2;
    assert (3 * x + 11) % 2 == 1;
    assert isOdd(nineteens(x));
}

function relationDomain<T>(s: set<(T,T)>): set<T> {
    set z | z in s :: z.1
}

predicate reflexive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall s :: s in S ==> (s,s) in R
}

predicate symmetric<T>(R: set<(T,T)>, S: set<T>)
    requires relationOnASet(R, S)
{
    forall x: T, y:T :: x in S && y in S && (x,y) in R ==> (y, x) in R
}

predicate transitive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall a,b,c :: a in S && b in S && c in S && (a,b) in R && (b,c) in R ==> (a,c) in R
}

predicate equivalenceRelation<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    reflexive(R, S) && symmetric(R, S) && transitive(R, S)
}

predicate relationOnASet<T>(R: set<(T,T)>, S: set<T>) {
    forall ts :: ts in R ==> ts.0 in S && ts.1 in S
}

// lemma equivUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
//     requires |R_1| > 0
//     requires |R_2| > 0
//     requires |S_1| > 0
//     requires |S_2| > 0
//     requires relationOnASet(R_1, S_1)
//     requires relationOnASet(R_2, S_2)
//     requires equivalenceRelation(R_1, S_1)
//     requires equivalenceRelation(R_2, S_2)
//     ensures equivalenceRelation(R_1+R_2, S_1+S_2)
// {
//     reflexiveUnion(R_1, S_1, R_2, S_2);
//     symmetricUnion(R_1, S_1, R_2, S_2);
//     transitiveUnion(R_1, S_1, R_2, S_2);
// }

lemma reflexiveUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
    requires |R_1| > 0
    requires |R_2| > 0
    requires |S_1| > 0
    requires |S_2| > 0
    requires relationOnASet(R_1, S_1)
    requires relationOnASet(R_2, S_2)
    requires reflexive(R_1, S_1)
    requires reflexive(R_2, S_2)
    ensures reflexive(R_1+R_2, S_1+S_2)
{
    forall s | s in S_1 + S_2
        ensures (s,s) in R_1 + R_2
    {
        if s in S_1 {
            assert (s,s) in R_1;
            assert (s,s) in R_1 + R_2;
        } else if s in S_2 {
            assert (s,s) in R_2;
            assert (s,s) in R_1 + R_2;
        }
    }
}

lemma symmetricUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
    requires |R_1| > 0
    requires |R_2| > 0
    requires |S_1| > 0
    requires |S_2| > 0
    requires relationOnASet(R_1, S_1)
    requires relationOnASet(R_2, S_2)
    requires symmetric(R_1, S_1)
    requires symmetric(R_2, S_2)
    ensures symmetric(R_1+R_2, S_1+S_2)
{
    // assert R_1 <= (R_1+R_2);
    // assert R_2 <= (R_1+R_2);
    // assert symmetric(R_1, S_1);
    // assert symmetric(R_2, S_2);
    forall x,y | x in S_1+S_2 && y in S_1+S_2 && (x,y) in R_1+R_2
        ensures (y,x) in R_1+R_2
    {
        if  x in S_1 && y in S_1 && (x,y) in R_1 {
            assert (y,x) in R_1;
            assert (y,x) in R_1+R_2;
        }else if  x in S_2 && y in S_2 && (x,y) in R_2 {
            assert (y,x) in R_2;
            assert (y,x) in R_1+R_2;
        }
    }
}

    
lemma transitiveUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
    requires |R_1| > 0
    requires |R_2| > 0
    requires |S_1| > 0
    requires |S_2| > 0
    requires relationOnASet(R_1, S_1)
    requires relationOnASet(R_2, S_2)
    requires transitive(R_1, S_1)
    requires transitive(R_2, S_2)
    ensures transitive(R_1+R_2, S_1+S_2) 
{

    assume forall a :: a in S_1+S_2 ==> a !in S_1 || a !in S_2;

    forall a,b,c | a in S_1+S_2 && b in S_1+S_2 && c in S_1+S_2 && (a,b) in R_1+R_2 && (b,c) in R_1+R_2 
        ensures (a,c) in R_1+R_2
    {
        if a in S_1 && b in S_1 && c in S_1 && (a,b) in R_1 && (b,c) in R_1 {
            assert (a,c) in R_1;
            assert (a,c) in R_1+R_2;
        }else if a in S_2 && b in S_2 && c in S_2 && (a,b) in R_2 && (b,c) in R_2 {
            assert (a,c) in R_2;
            assert (a,c) in R_1+R_2;
        }
    } 
}

// lemma transitiveUnionContra<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
//     requires |R_1| > 0
//     requires |R_2| > 0
//     requires |S_1| > 0
//     requires |S_2| > 0
//     requires relationOnASet(R_1, S_1)
//     requires relationOnASet(R_2, S_2)
//     requires transitive(R_1, S_1)
//     requires transitive(R_2, S_2)
//     ensures exists (R_1+R_2, S_1+S_2) :: !transitive(R_1+R_2, S_1+S_2) 
// {
//     assume S_1 * S_2 != {};
//     if transitive(R_1 + R_2, S_1+S_2) {
//         forall a,b,c | a in S_1+S_2 && b in S_1+S_2 && c in S_1+S_2 && (a,b) in R_1+R_2 && (b,c) in R_1+R_2 
//             ensures (a,c) in R_1+R_2 
//         {
//             if a in S_1 && a !in S_2 && b in S_1 && b in S_2 && c in S_2 && c !in S_1 {
//                 assert (a,c) !in R_1;
//                 assert (a,c) !in R_2;
//                 assert (a,c) !in R_1+R_2;
//                 assert false;
//             }
//         } 
//     }
// }

lemma transitiveUnionContra<T>()
  returns (
  R1: set<(T, T)>, S1: set<T>,
  R2: set<(T, T)>, S2: set<T>)
  ensures relationOnASet(R1, S1)
  ensures relationOnASet(R2, S2)
  ensures transitive(R1, S1)
  ensures transitive(R2, S2)
  ensures ! transitive(R1 + R2, S1 + S2)
{
  var a : T :| assume true;
  var b : T :| assume a != b;
  var c : T :| assume a != c && b != c;
  S1 := {a, b};
  S2 := {b, c};
  R1 := {(a, b)};
  R2 := {(b, c)};
  // Annotations to show all required properties
  assert relationOnASet(R1, S1);
  assert relationOnASet(R2, S2);
  assert transitive(R1, S1);
  assert transitive(R2, S2);
  // Show that (a,b) in R1, (b,c) in R2, but (a,c) not in R1+R2
  assert (a,b) in R1+R2;
  assert (b,c) in R1+R2;
  assert (a in S1+S2 && b in S1+S2 && c in S1+S2);
  assert (a,c) !in R1+R2;
}

lemma notTrueAlways<T>()
  ensures !
  (forall S1 : set<T>, S2 : set<T>, R1 : set<(T,T)>, R2 : set<(T, T)> ::
  relationOnASet(R1, S1) &&
  relationOnASet(R2, S2) &&
  transitive(R1, S1) &&
  transitive(R2, S2)  ==> transitive(R1 + R2, S1 + S2)
  )
{
  var a, b, c, d := transitiveUnionContra<T>();
  // assert !transitive(a + c, b + d);
}

method test() {
    var x := 7;
    assert isEven(eight(7));
    var four := 4;
    // var test := set x: nat,y: nat | 1 <= x <= y <= 5 :: (x,y);
    var sample := {1,2,3,4,5,6};
    var test := set x,y | x in sample  && y in sample :: (x,y);
    var modulos := set x,y | x in sample && y in sample && x % y == 0 :: (x,y);
    assert reflexive(test, sample);
    // assert equivalenceRelation(modulos, sample);

    var hmm := (1,2,3);
    assert 0 <= four < 100 && isEven(nineteenf(four));
    ghost var y: nat  :| isEven(nineteenf(y));
}

function abs(a: real) : real {if a>0.0 then a else -a}
