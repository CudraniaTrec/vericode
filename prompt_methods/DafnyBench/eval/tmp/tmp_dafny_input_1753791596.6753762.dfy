// Proving type safety of a Simply Typed Lambda-Calculus in Dafny
// adapted from Coq (http://www.cis.upenn.edu/~bcpierce/sf/Stlc.html)

datatype option<A> = None | Some(get: A)

// Types
datatype ty =  TBase
            |  TArrow(T1: ty, T2: ty)

// Terms
datatype tm = tvar(id: int)
            | tapp(f: tm, arg: tm)
            | tabs(x: int, T: ty, body: tm)

// Values
predicate value(t: tm)
{
  t.tabs?
}

// Free Variables and Substitution

function method fv(t: tm): set<int>
{
  match t
  case tvar(id) => {id}
  case tabs(x, T, body) => fv(body) - {x}
  case tapp(f, arg) => fv(f) + fv(arg)
}

function method subst(x: int, s: tm, t: tm): tm
{
  match t
  case tvar(x') => if x == x' then s else t
  case tabs(x', T, t1) => tabs(x', T, if x == x' then t1 else subst(x, s, t1))
  case tapp(t1, t2) => tapp(subst(x, s, t1), subst(x, s, t2))
}

// Reduction
function method step(t: tm): option<tm>
{
  if t.tapp? && t.f.tabs? && value(t.arg) then
    Some(subst(t.f.x, t.arg, t.f.body))
  else if t.tapp? && step(t.f).Some? then
    Some(tapp(step(t.f).get, t.arg))
  else if t.tapp? && value(t.f) && step(t.arg).Some? then
    Some(tapp(t.f, step(t.arg).get))
  else
    None
}

predicate reduces_to(t: tm, t': tm, n: nat)
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n-1))
}

lemma lemma_step_example1(n: nat)
  requires n > 0;
  ensures reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                     tabs(0, TBase, tvar(0)), n);
{
  // Strongest annotation: show the reduction in one step, then use reduces_to
  assert step(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0)))).Some?;
  assert step(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0)))).get == tabs(0, TBase, tvar(0));
  assert reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                    tabs(0, TBase, tvar(0)), n);
}

// Typing

function method find(c: map<int,ty>, x: int): option<ty>
{
  if x in c then Some(c[x]) else None
}
function method extend(x: int, T: ty, c: map<int,ty>): map<int,ty>
{
  c[x := T]
}

function method has_type(c: map<int,ty>, t: tm): option<ty>
{
  match t
  case tvar(id) => find(c, id)
  case tabs(x, T, body) =>
    var ty_body := has_type(extend(x, T, c), body);
    if ty_body.Some? then Some(TArrow(T, ty_body.get)) else None
  case tapp(f, arg) =>
    var ty_f := has_type(c, f);
    var ty_arg := has_type(c, arg);
    if ty_f.Some? && ty_arg.Some? then
      if ty_f.get.TArrow? && ty_f.get.T1 == ty_arg.get then
        Some(ty_f.get.T2)
      else
        None
    else
      None
}

lemma example_typing_1()
  ensures has_type(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase));
{
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
  assert has_type(c, tapp(tvar(0), tvar(0))) == (if S.TArrow? && S.T1 == S then Some(S.T2) else None);
  assert has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) == (if S.TArrow? && S.T1 == S then Some(TArrow(S, S.T2)) else None);
  assert has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T);
}

// Progress
lemma theorem_progress(t: tm)
  requires has_type(map[], t).Some?;
  ensures value(t) || step(t).Some?;
{
  if t.tabs? {
    assert value(t);
  } else if t.tapp? {
    var ty_f := has_type(map[], t.f);
    var ty_arg := has_type(map[], t.arg);
    assert ty_f.Some? && ty_arg.Some?;
    if !value(t.f) {
      assert step(t.f).Some? || value(t.f);
      if step(t.f).Some? {
        assert step(t).Some?;
      }
    } else if !value(t.arg) {
      assert step(t.arg).Some? || value(t.arg);
      if step(t.arg).Some? {
        assert step(t).Some?;
      }
    } else {
      assert t.f.tabs?;
      assert step(t).Some?;
    }
  }
}

// Free-in-context
lemma {:induction c, t} lemma_free_in_context(c: map<int,ty>, x: int, t: tm)
  requires x in fv(t);
  requires has_type(c, t).Some?;
  ensures find(c, x).Some?;
{
  if t.tvar? {
    assert t.id == x;
    assert find(c, x).Some?;
  }
  if t.tabs? {
    if x != t.x {
      lemma_free_in_context(extend(t.x, t.T, c), x, t.body);
    }
  }
  if t.tapp? {
    if x in fv(t.f) {
      lemma_free_in_context(c, x, t.f);
    } else {
      lemma_free_in_context(c, x, t.arg);
    }
  }
}

// Closed
predicate closed(t: tm)
{
  forall x :: x !in fv(t)
}

lemma corollary_typable_empty__closed(t: tm)
  requires has_type(map[], t).Some?;
  ensures closed(t);
{
  forall (x:int)
    ensures x !in fv(t)
  {
    if x in fv(t) {
      lemma_free_in_context(map[], x, t);
      assert false;
    }
  }
}

// Context invariance
lemma {:induction t} lemma_context_invariance(c: map<int,ty>, c': map<int,ty>, t: tm)
  requires has_type(c, t).Some?;
  requires forall x: int :: x in fv(t) ==> find(c, x) == find(c', x);
  ensures has_type(c, t) == has_type(c', t);
{
  if t.tabs? {
    lemma_context_invariance(extend(t.x, t.T, c), extend(t.x, t.T, c'), t.body);
  }
  if t.tapp? {
    lemma_context_invariance(c, c', t.f);
    lemma_context_invariance(c, c', t.arg);
  }
}

// Substitution preserves typing
lemma lemma_substitution_preserves_typing(c: map<int,ty>, x: int, s: tm, t: tm)
  requires has_type(map[], s).Some?;
  requires has_type(extend(x, has_type(map[], s).get, c), t).Some?;
  ensures has_type(c, subst(x, s, t)) == has_type(extend(x, has_type(map[], s).get, c), t);
{
  var S := has_type(map[], s).get;
  var cs := extend(x, S, c);
  var T  := has_type(cs, t).get;

  if t.tvar? {
    if t.id == x {
      corollary_typable_empty__closed(s);
      lemma_context_invariance(map[], c, s);
    }
  }
  if t.tabs? {
    if t.x == x {
      lemma_context_invariance(cs, c, t);
    } else {
      var cx  := extend(t.x, t.T, c);
      var csx := extend(x, S, cx);
      var cxs := extend(t.x, t.T, cs);
      lemma_context_invariance(cxs, csx, t.body);
      lemma_substitution_preserves_typing(cx, x, s, t.body);
    }
  }
  if t.tapp? {
    lemma_substitution_preserves_typing(c, x, s, t.f);
    lemma_substitution_preserves_typing(c, x, s, t.arg);
  }
}

// Preservation
lemma theorem_preservation(t: tm)
  requires has_type(map[], t).Some?;
  requires step(t).Some?;
  ensures has_type(map[], step(t).get) == has_type(map[], t);
{
  if t.tapp? && t.f.tabs? && value(t.arg) {
    lemma_substitution_preserves_typing(map[], t.f.x, t.arg, t.f.body);
  }
  if t.tapp? && step(t.f).Some? {
    lemma theorem_preservation(t.f);
  }
  if t.tapp? && value(t.f) && step(t.arg).Some? {
    lemma theorem_preservation(t.arg);
  }
}

predicate normal_form(t: tm)
{
  step(t).None?
}

predicate stuck(t: tm)
{
  normal_form(t) && !value(t)
}

lemma corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  requires has_type(map[], t) == Some(T);
  requires reduces_to(t, t', n);
  ensures !stuck(t');
{
  if t == t' {
    theorem_progress(t');
    assert !stuck(t');
  } else {
    assert n > 0;
    assert step(t).Some?;
    theorem_preservation(t);
    corollary_soundness(step(t).get, t', T, n-1);
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
