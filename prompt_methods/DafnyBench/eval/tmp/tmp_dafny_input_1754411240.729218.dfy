module Ints {
  const U32_BOUND: nat := 0x1_0000_0000
  newtype u32 = x:int | 0 <= x < 0x1_0000_0000
  newtype i32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
}

module Lang {
  import opened Ints

  datatype Reg = R0 | R1 | R2 | R3

  datatype Expr =
    | Const(n: u32)
      // overflow during addition is an error
    | Add(r1: Reg, r2: Reg)
      // this is saturating subtraction (to allow comparing numbers)
    | Sub(r1: Reg, r2: Reg)

  datatype Stmt =
    | Assign(r: Reg, e: Expr)
      // Jump by offset if condition is true
    | JmpZero(r: Reg, offset: i32)

  datatype Program = Program(stmts: seq<Stmt>)

}

/* Well-formed check: offsets are all within the program */
/* Main safety property: additions do not overflow */

/* First, we give the concrete semantics of programs. */

module ConcreteEval {
  import opened Ints
  import opened Lang

  type State = Reg -> u32

  function update_state(s: State, r0: Reg, v: u32): State {
    ((r: Reg) => if r == r0 then v else s(r))
  }

  datatype Option<T> = Some(v: T) | None

  function expr_eval(env: State, e: Expr): Option<u32>
    ensures e.Const? ==> expr_eval(env, e) == Option.Some(e.n)
    ensures e.Add? ==>
      (env(e.r1) as int + env(e.r2) as int >= U32_BOUND ==> expr_eval(env, e) == Option.None) &&
      (env(e.r1) as int + env(e.r2) as int < U32_BOUND ==> expr_eval(env, e) == Option.Some(env(e.r1) + env(e.r2)))
    ensures e.Sub? ==>
      (env(e.r1) as int - env(e.r2) as int < 0 ==> expr_eval(env, e) == Option.Some(0)) &&
      (env(e.r1) as int - env(e.r2) as int >= 0 ==> expr_eval(env, e) == Option.Some(env(e.r1) - env(e.r2)))
  {
    match e {
      case Const(n) => Some(n)
      case Add(r1, r2) =>
        if env(r1) as int + env(r2) as int >= U32_BOUND then None
        else Some(env(r1) + env(r2))
      case Sub(r1, r2) =>
        if env(r1) as int - env(r2) as int < 0 then Some(0)
        else Some(env(r1) - env(r2))
    }
  }

  // stmt_step executes a single statement
  //
  // Returns a new state and a relative PC offset (which is 1 for non-jump
  // statements).
  function stmt_step(env: State, s: Stmt): Option<(State, int)>
    ensures s.Assign? ==>
      (expr_eval(env, s.e).Some? ==> stmt_step(env, s) == Option.Some((update_state(env, s.r, expr_eval(env, s.e).v), 1))) &&
      (expr_eval(env, s.e).None? ==> stmt_step(env, s) == Option.None)
    ensures s.JmpZero? ==>
      stmt_step(env, s) == Option.Some((env, (if env(s.r) == 0 then s.offset else 1) as int))
  {
    match s {
      case Assign(r, e) =>
        var e' := expr_eval(env, e);
        match e' {
          case Some(v) => Some((update_state(env, r, v), 1))
          case None => None
        }
      case JmpZero(r, offset) =>
        Some((env, (if env(r) == 0 then offset else 1) as int))
    }
  }

  datatype ExecResult = Ok(env: State) | NoFuel | Error

  // Run a program starting at pc.
  //
  // The sequence of statements is constant, meant to reflect a static program.
  // Termination occurs if the pc ever reaches exactly the end.
  //
  // Errors can come from either executing statements (see stmt_step for those
  // errors), or from an out-of-bounds pc (negative or not past the end of ss).
  //
  // fuel is needed to make this function terminate; the idea is that if there
  // exists some fuel that makes the program terminate, that is it's complete
  // execution, and if it always runs out of fuel it has an infinite loop.
  function stmts_step(env: State, ss: seq<Stmt>, pc: nat, fuel: nat): ExecResult
    requires pc <= |ss|
    ensures fuel == 0 ==> stmts_step(env, ss, pc, fuel) == ExecResult.NoFuel
    ensures pc == |ss| ==> stmts_step(env, ss, pc, fuel) == ExecResult.Ok(env)
    ensures pc < |ss| && fuel > 0 && stmt_step(env, ss[pc]).None? ==> stmts_step(env, ss, pc, fuel) == ExecResult.Error
    ensures pc < |ss| && fuel > 0 && stmt_step(env, ss[pc]).Some? && !(0 <= pc + stmt_step(env, ss[pc]).v.1 <= |ss|) ==> stmts_step(env, ss, pc, fuel) == ExecResult.Error
    decreases fuel
  {
    if fuel == 0 then NoFuel
    else if pc == |ss| then Ok(env)
    else
      if stmt_step(env, ss[pc]).None? then Error
      else
        // At this point, stmt_step(env, ss[pc]) is Some((env', offset))
        var env'_offset := stmt_step(env, ss[pc]).v;
        if !(0 <= pc + env'_offset.1 <= |ss|) then Error
        else stmts_step(env'_offset.0, ss, pc + env'_offset.1, fuel - 1)
  }

}

/* Now we turn to analyzing programs */

module AbstractEval {
  import opened Ints
  import opened Lang

  datatype Val = Interval(lo: int, hi: int)

  datatype AbstractState = AbstractState(rs: Reg -> Val)

  function expr_eval(env: AbstractState, e: Expr): Val
    ensures e.Const? ==> expr_eval(env, e) == Interval(e.n as int, e.n as int)
    ensures e.Add? ==>
      expr_eval(env, e) == Interval(env.rs(e.r1).lo + env.rs(e.r2).lo, env.rs(e.r1).hi + env.rs(e.r2).hi)
    ensures e.Sub? ==>
      expr_eval(env, e) == Interval(0, if env.rs(e.r1).hi - env.rs(e.r2).lo >= 0 then env.rs(e.r1).hi - env.rs(e.r2).lo else 0)
  {
    match e {
      case Const(n) => Interval(n as int, n as int)
      case Add(r1, r2) =>
        var v1 := env.rs(r1);
        var v2 := env.rs(r2);
        Interval(v1.lo + v2.lo, v1.hi + v2.hi)
      case Sub(r1, r2) =>
        var v1 := env.rs(r1);
        var v2 := env.rs(r2);
        Interval(0, if v1.hi - v2.lo >= 0 then v1.hi - v2.lo else 0)
    }
  }

  function update_state(env: AbstractState, r0: Reg, v: Val): AbstractState
    ensures forall r: Reg :: r == r0 ==> update_state(env, r0, v).rs(r) == v
    ensures forall r: Reg :: r != r0 ==> update_state(env, r0, v).rs(r) == env.rs(r)
  {
    AbstractState((r: Reg) => if r == r0 then v else env.rs(r))
  }

  // function stmt_step(env: State, s: Stmt): Option<(State, int)>
  function stmt_eval(env: AbstractState, s: Stmt): (AbstractState, set<int>)
    ensures s.Assign? ==> stmt_eval(env, s).0 == update_state(env, s.r, expr_eval(env, s.e)) && stmt_eval(env, s).1 == {1}
    ensures s.JmpZero? ==> stmt_eval(env, s).0 == env && stmt_eval(env, s).1 == {s.offset as int, 1}
  {
    match s {
      case Assign(r, e) => var v := expr_eval(env, e);
                           (update_state(env, r, v), {1 as int})
      case JmpZero(r, offset) =>
        (env, {offset as int, 1})
    }
  }

  // Check that jump targets ss[from..] are valid.
  function has_valid_jump_targets(ss: seq<Stmt>, from: nat): bool
    requires from <= |ss|
    ensures has_valid_jump_targets(ss, from) <==>
            (forall i | from <= i < |ss| :: ss[i].JmpZero? ==> 0 <= i + ss[i].offset as int <= |ss|)
    decreases |ss| - from
  {
    if from == |ss| then true
    else (match ss[from] {
            case JmpZero(_, offset) =>
              0 <= from + offset as int <= |ss|
            case _ => true
          } &&
          has_valid_jump_targets(ss, from+1))
  }

  ghost predicate valid_jump_targets(ss: seq<Stmt>) {
    forall i | 0 <= i < |ss| :: ss[i].JmpZero? ==> 0 <= i + ss[i].offset as int <= |ss|
  }

  lemma has_valid_jump_targets_ok_helper(ss: seq<Stmt>, from: nat)
    requires from <= |ss|
    ensures has_valid_jump_targets(ss, from) <==>
            (forall i | from <= i < |ss| :: ss[i].JmpZero? ==> 0 <= i + ss[i].offset as int <= |ss|)
    decreases |ss| - from
  {
    if from == |ss| {
    } else {
      has_valid_jump_targets_ok_helper(ss, from+1);
    }
  }

  lemma has_valid_jump_targets_ok(ss: seq<Stmt>)
    ensures has_valid_jump_targets(ss, 0) <==> valid_jump_targets(ss)
  {
    has_valid_jump_targets_ok_helper(ss, 0);
  }
}

module AbstractEvalProof {
  import opened Ints
  import opened Lang
  import E = ConcreteEval
  import opened AbstractEval

  /* What does it mean for a concrete state to be captured by an abstract state?
   * (Alternately, interpret each abstract state as a set of concrete states) */

  ghost predicate reg_included(c_v: u32, v: Val) {
    v.lo <= c_v as int <= v.hi
  }

  ghost predicate state_included(env: E.State, abs: AbstractState) {
    forall r: Reg :: reg_included(env(r), abs.rs(r))
  }

  lemma expr_eval_ok(env: E.State, abs: AbstractState, e: Expr)
    requires state_included(env, abs)
    requires E.expr_eval(env, e).Some?
    ensures reg_included(E.expr_eval(env, e).v, expr_eval(abs, e))
  {
    match e {
      case Add(r1, r2) => {
        var v1 := env(r1);
        var v2 := env(r2);
        var a1 := abs.rs(r1);
        var a2 := abs.rs(r2);
        assert a1.lo <= v1 as int <= a1.hi;
        assert a2.lo <= v2 as int <= a2.hi;
        assert v1 as int + v2 as int < Ints.U32_BOUND;
        assert a1.lo + a2.lo <= v1 as int + v2 as int <= a1.hi + a2.hi;
      }
      case Const(n) => {
        assert expr_eval(abs, e) == Interval(n as int, n as int);
        assert E.expr_eval(env, e) == E.Option.Some(n);
        assert reg_included(n, Interval(n as int, n as int));
      }
      case Sub(r1, r2) => {
        var v1 := env(r1);
        var v2 := env(r2);
        var a1 := abs.rs(r1);
        var a2 := abs.rs(r2);
        assert a1.lo <= v1 as int <= a1.hi;
        assert a2.lo <= v2 as int <= a2.hi;
        if v1 <= v2 {
          assert E.expr_eval(env, e) == E.Option.Some(0);
          assert 0 >= a1.lo - a2.hi;
          assert 0 <= expr_eval(abs, e).hi;
          assert reg_included(0, expr_eval(abs, e));
        } else {
          assert E.expr_eval(env, e) == E.Option.Some(v1 - v2);
          assert v1 as int - v2 as int >= 0;
          assert 0 <= v1 as int - v2 as int <= a1.hi - a2.lo;
          assert 0 <= v1 as int - v2 as int <= expr_eval(abs, e).hi;
          assert reg_included(v1 - v2, expr_eval(abs, e));
        }
      }
    }
  }

  lemma stmt_eval_ok(env: E.State, abs: AbstractState, stmt: Stmt)
    requires state_included(env, abs)
    requires E.stmt_step(env, stmt).Some?
    ensures state_included(E.stmt_step(env, stmt).v.0, stmt_eval(abs, stmt).0)
  {
    match stmt {
      case Assign(r, e) => {
        assert E.expr_eval(env, e).Some?;
        expr_eval_ok(env, abs, e);
        var v := E.expr_eval(env, e).v;
        var av := expr_eval(abs, e);
        assert reg_included(v, av);
        // For all r':Reg, show reg_included(E.stmt_step(env, stmt).v.0(r'), stmt_eval(abs, stmt).0.rs(r'))
        // If r' == r: updated to v/av, else unchanged
        assert forall r':Reg :: (r' == r ==> reg_included(E.stmt_step(env, stmt).v.0(r'), av)) &&
                                   (r' != r ==> reg_included(E.stmt_step(env, stmt).v.0(r'), abs.rs(r')));
      }
      case JmpZero(r, offset) => {
        assert E.stmt_step(env, stmt).v.0 == env;
        assert stmt_eval(abs, stmt).0 == abs;
        assert state_included(env, abs);
      }
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
