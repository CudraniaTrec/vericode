
﻿// Proving type safety of a Simply Typed Lambda-Calculus in Dafny
// adapted from Coq (http://www.cis.upenn.edu/~bcpierce/sf/Stlc.html)

/// Utilities

// ... handy for partial functions
datatype option<A> = None | Some(get: A)

/// -----
/// Model
/// -----

/// Syntax

// Types
datatype ty =  TBase                             // (opaque base type)
            |  TArrow(T1: ty, T2: ty)            // T1 => T2
/*BOOL?
            | TBool                              // (base type for booleans)
?BOOL*/
/*NAT?
            |  TNat                              // (base type for naturals)
?NAT*/
/*REC?
            | TVar(id: int) | TRec(X: nat, T: ty)// (iso-recursive types)
?REC*/

// Terms
datatype tm = tvar(id: int)                      // x                  (variable)
            | tapp(f: tm, arg: tm)               // t t                (application)
            | tabs(x: int, T: ty, body: tm)      // \x:T.t             (abstraction)
/*BOOL?
            | ttrue | tfalse                     // true, false        (boolean values)
            | tif(c: tm, a: tm, b: tm)           // if t then t else t (if expression)
?BOOL*/
/*NAT?
            | tzero | tsucc(p: tm) | tprev(n: tm)//                    (naturals)
/*BOOL?
            | teq(n1: tm, n2: tm)                //                    (equality on naturals)
?BOOL*/
?NAT*/
/*REC?
            | tfold(Tf: ty, tf: tm) | tunfold(tu: tm)//                (iso-recursive terms)
?REC*/

/// Operational Semantics

// Values
predicate value(t: tm)
{
  t.tabs?
/*BOOL?
  || t.ttrue? || t.tfalse?
?BOOL*/
/*NAT?
  || peano(t)
?NAT*/
/*REC?
  || (t.tfold? && value(t.tf))
?REC*/
}

/*NAT?
predicate peano(t: tm)
{
  t.tzero? || (t.tsucc? && peano(t.p))
}
?NAT*/

// Free Variables and Substitution

function fv(t: tm): set<int> //of free variables of t
{
  match t
  // interesting cases...
  case tvar(id) => {id}
  case tabs(x, T, body) => fv(body)-{x}//x is bound
  // congruent cases...
  case tapp(f, arg) => fv(f)+fv(arg)
/*BOOL?
  case tif(c, a, b) => fv(a)+fv(b)+fv(c)
  case ttrue => {}
  case tfalse => {}
?BOOL*/
/*NAT?
  case tzero => {}
  case tsucc(p) => fv(p)
  case tprev(n) => fv(n)
/*BOOL?
  case teq(n1, n2) => fv(n1)+fv(n2)
?BOOL*/
?NAT*/
/*REC?
  case tfold(T, t1) => fv(t1)
  case tunfold(t1) => fv(t1)
?REC*/
}

function subst(x: int, s: tm, t: tm): tm //[x -> s]t
{
  match t
  // interesting cases...
  case tvar(x') => if x==x' then s else t
  // N.B. only capture-avoiding if s is closed...
  case tabs(x', T, t1) => tabs(x', T, if x==x' then t1 else subst(x, s, t1))
  // congruent cases...
  case tapp(t1, t2) => tapp(subst(x, s, t1), subst(x, s, t2))
/*BOOL?
  case ttrue => ttrue
  case tfalse => tfalse
  case tif(t1, t2, t3) => tif(subst(x, s, t1), subst(x, s, t2), subst(x, s, t3))
?BOOL*/
/*NAT?
  case tzero => tzero
  case tsucc(p) => tsucc(subst(x, s, p))
  case tprev(n) => tprev(subst(x, s, n))
/*BOOL?
  case teq(n1, n2) => teq(subst(x, s, n1), subst(x, s, n2))
?BOOL*/
?NAT*/
/*REC?
  case tfold(T, t1) => tfold(T, subst(x, s, t1))
  case tunfold(t1) => tunfold(subst(x, s, t1))
?REC*/
}

/*REC?
function ty_fv(T: ty): set<int> //of free type variables of T
{
  match T
  case TVar(X) => {X}
  case TRec(X, T1) => ty_fv(T1)-{X}
  case TArrow(T1, T2) => ty_fv(T1)+ty_fv(T2)
  case TBase => {}
/*BOOL?
  case TBool => {}
?BOOL*/
/*NAT?
  case TNat => {}
?NAT*/
}

function tsubst(X: int, S: ty, T: ty): ty
{
  match T
  case TVar(X') => if X==X' then S else T
  case TRec(X', T1) => TRec(X', if X==X' then T1 else tsubst(X, S, T1))
  case TArrow(T1, T2) => TArrow(tsubst(X, S, T1), tsubst(X, S, T2))
  case TBase => TBase
/*BOOL?
  case TBool => TBool
?BOOL*/
/*NAT?
  case TNat => TNat
?NAT*/
}

predicate ty_closed(T: ty)
{
  forall x :: x !in ty_fv(T)
}
?REC*/

// Reduction
function step(t: tm): option<tm>
{
  /* AppAbs */     if (t.tapp? && t.f.tabs? && value(t.arg)) then
  Some(subst(t.f.x, t.arg, t.f.body))
  /* App1 */       else if (t.tapp? && step(t.f).Some?) then
  Some(tapp(step(t.f).get, t.arg))
  /* App2 */       else if (t.tapp? && value(t.f) && step(t.arg).Some?) then
  Some(tapp(t.f, step(t.arg).get))
/*BOOL?
  /* IfTrue */     else if (t.tif? && t.c == ttrue) then
  Some(t.a)
  /* IfFalse */    else if (t.tif? && t.c == tfalse) then
  Some(t.b)
  /* If */         else if (t.tif? && step(t.c).Some?) then
  Some(tif(step(t.c).get, t.a, t.b))
?BOOL*/
/*NAT?
  /* Prev0 */
                   else if (t.tprev? && t.n.tzero?) then
  Some(tzero)
  /* PrevSucc */   else if (t.tprev? && peano(t.n) && t.n.tsucc?) then
  Some(t.n.p)
  /* Prev */       else if (t.tprev? && step(t.n).Some?) then
  Some(tprev(step(t.n).get))
  /* Succ */       else if (t.tsucc? && step(t.p).Some?) then
  Some(tsucc(step(t.p).get))
/*BOOL?
  /* EqTrue0 */    else if (t.teq? && t.n1.tzero? && t.n2.tzero?) then
  Some(ttrue)
  /* EqFalse1 */   else if (t.teq? && t.n1.tsucc? && peano(t.n1) && t.n2.tzero?) then
  Some(tfalse)
  /* EqFalse2 */   else if (t.teq? && t.n1.tzero? && t.n2.tsucc? && peano(t.n2)) then
  Some(tfalse)
  /* EqRec */      else if (t.teq? && t.n1.tsucc? && t.n2.tsucc? && peano(t.n1) && peano(t.n2)) then
  Some(teq(t.n1.p, t.n2.p))
  /* Eq1 */        else if (t.teq? && step(t.n1).Some?) then
  Some(teq(step(t.n1).get, t.n2))
  /* Eq2 */        else if (t.teq? && peano(t.n1) && step(t.n2).Some?) then
  Some(teq(t.n1, step(t.n2).get))
?BOOL*/
?NAT*/
/*REC?
  /* UnfoldFold */ else if (t.tunfold? && t.tu.tfold? && value(t.tu.tf)) then Some(t.tu.tf)
  /* Fold */       else if (t.tfold? && step(t.tf).Some?) then Some(tfold(t.Tf, step(t.tf).get))
  /* Unfold */     else if (t.tunfold? && step(t.tu).Some?) then Some(tunfold(step(t.tu).get))
?REC*/
  else None
}

// Multistep reduction:
// The term t reduces to the term t' in n or less number of steps.
predicate reduces_to(t: tm, t': tm, n: nat)
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n-1))
}

// Examples
lemma lemma_step_example1(n: nat)
  requires n > 0;
  // (\x:B=>B.x) (\x:B.x) reduces to (\x:B.x)
  ensures reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                     tabs(0, TBase, tvar(0)), n);
{
  // Strongest annotation: show the reduction in one step, then use reduces_to
  assert step(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0)))).Some?;
  assert step(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0)))).get == tabs(0, TBase, tvar(0));
  assert reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                    tabs(0, TBase, tvar(0)), n);
}


/// Typing

// A context is a partial map from variable names to types.
function find(c: map<int,ty>, x: int): option<ty>
{
  if (x in c) then Some(c[x]) else None
}
function extend(x: int, T: ty, c: map<int,ty>): map<int,ty>
{
  c[x:=T]
}

// Typing Relation
function has_type(c: map<int,ty>, t: tm): option<ty>
{
  match t
  /* Var */  case tvar(id) => find(c, id)
  /* Abs */  case tabs(x, T, body) =>
  var ty_body := has_type(extend(x, T, c), body);
                     if (ty_body.Some?) then
  Some(TArrow(T, ty_body.get))          else None
  /* App */  case tapp(f, arg) =>
  var ty_f   := has_type(c, f);
  var ty_arg := has_type(c, arg);
                     if (ty_f.Some? && ty_arg.Some?) then
  if ty_f.get.TArrow? && ty_f.get.T1 == ty_arg.get then
  Some(ty_f.get.T2)  else None else None
/*BOOL?
  /* True */  case ttrue => Some(TBool)
  /* False */ case tfalse => Some(TBool)
  /* If */    case tif(cond, a, b) =>
  var ty_c := has_type(c, cond);
  var ty_a := has_type(c, a);
  var ty_b := has_type(c, b);
                     if (ty_c.Some? && ty_a.Some? && ty_b.Some?) then
  if ty_c.get == TBool && ty_a.get == ty_b.get then
  ty_a
                     else None else None
?BOOL*/
/*NAT?
  /* Zero */  case tzero => Some(TNat)
  /* Prev */  case tprev(n) =>
  var ty_n := has_type(c, n);
                     if (ty_n.Some?) then
  if ty_n.get == TNat then
  Some(TNat)         else None else None
  /* Succ */  case tsucc(p) =>
  var ty_p := has_type(c, p);
                     if (ty_p.Some?) then
  if ty_p.get == TNat then
  Some(TNat)         else None else None
/*BOOL?
  /* Eq */    case teq(n1, n2) =>
  var ty_n1 := has_type(c, n1);
  var ty_n2 := has_type(c, n2);
                      if (ty_n1.Some? && ty_n2.Some?) then
  if ty_n1.get == TNat && ty_n2.get == TNat then
  Some(TBool)         else None else None
?BOOL*/
?NAT*/
/*REC?
  /* Fold */  case tfold(U, t1) =>
  var ty_t1 := if (ty_closed(U)) then has_type(c, t1) else None;
                      if (ty_t1.Some?) then
  if U.TRec? && ty_t1.get==tsubst(U.X, U, U.T) then
  Some(U)             else None else None
  /* Unfold */ case tunfold(t1) =>
  var ty_t1 := has_type(c, t1);
                      if ty_t1.Some? then
  var U := ty_t1.get;
  if U.TRec? then
  Some(tsubst(U.X, U, U.T)) else None else None
?REC*/
}

// Examples

lemma example_typing_1()
  ensures has_type(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase));
{
  // Strongest annotation: show context and type for tvar(0)
  var c := extend(0, TBase, map[]);
  assert has_type(c, tvar(0)) == Some(TBase);
  assert has_type(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase));
}

lemma example_typing_2()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0)))))) ==
          Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)));
{
  var c := extend(1, TArrow(TBase, TBase), extend(0, TBase, map[]));
  assert has_type(c, tapp(tvar(1), tapp(tvar(1), tvar(0)))) == Some(TBase);
  assert has_type(extend(0, TBase, map[]), tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0)))))
         == Some(TArrow(TArrow(TBase, TBase), TBase));
  assert has_type(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0))))))
         == Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)));
}

lemma nonexample_typing_1()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1))))) == None;
{
  var c := extend(1, TBase, extend(0, TBase, map[]));
  assert has_type(c, tapp(tvar(0), tvar(1))) == None;
  assert has_type(extend(0, TBase, map[]), tabs(1, TBase, tapp(tvar(0), tvar(1)))) == None;
  assert has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1))))) == None;
}

lemma nonexample_typing_3(S: ty, T: ty)
  ensures has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T);
{
  var c := extend(0, S, map[]);
  // Strongest annotation: tvar(0) has type S, so tapp(tvar(0), tvar(0)) is only typable if S = TArrow(S', T') and S = S'
  // But in general, for arbitrary S and T, this cannot be Some(T)
  assert has_type(c, tapp(tvar(0), tvar(0))) == (if S.TArrow? && S.T1 == S then Some(S.T2) else None);
  assert has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) == (if S.TArrow? && S.T1 == S then Some(TArrow(S, S.T2)) else None);
  assert has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T);
}

/*BOOL?
lemma example_typing_bool()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tabs(2, TBool, tif(tvar(2), tvar(0), tvar(1)))))) ==
          Some(TArrow(TBase, TArrow(TBase, TArrow(TBool, TBase))));
{
  var c0 := extend(0, TBase, map[]);
  var c1 := extend(1, TBase, c0);
  var c2 := extend(2, TBool, c1);
  assert has_type(c2, tif(tvar(2), tvar(0), tvar(1))) == Some(TBase);
  assert has_type(c1, tabs(2, TBool, tif(tvar(2), tvar(0), tvar(1)))) == Some(TArrow(TBool, TBase));
  assert has_type(c0, tabs(1, TBase, tabs(2, TBool, tif(tvar(2), tva
function abs(a: real) : real {if a>0.0 then a else -a}
