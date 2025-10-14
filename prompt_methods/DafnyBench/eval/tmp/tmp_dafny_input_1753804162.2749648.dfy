
class CrashableMem<T> {
    var mem_ : array<T>;
    method read(off : int) returns (r : T)
        requires 0 <= off < mem_.Length;
        ensures r == mem_[off];
    {
        return mem_[off];
    }

    method write(off : int, val : T)
        requires 0 <= off < mem_.Length;
        modifies mem_;
        ensures mem_[off] == val;
        ensures forall i :: 0 <= i < mem_.Length && i != off ==> mem_[i] == old(mem_[i]);
    {
        mem_[off] := val;
    }
}

datatype GhostState = GS(
    num_entry : int,
    log : seq<int>,

    mem_len : int,
    mem : seq<int>,
    old_mem : seq<int>,
    ideal_mem : seq<int>,
    countdown : int,
    first_log_pos : map<int, int>
)

datatype GhostOp = WriteMem(off : int, val : int)
                 | WriteLog(off : int, val : int)
predicate ghost_state_inv(s : GhostState) {
    0 <= s.num_entry * 2 < |s.log|
    && |s.log| > 0
    && |s.mem| == s.mem_len && |s.ideal_mem| == s.mem_len && |s.old_mem| == s.mem_len
    && s.countdown >= 0
}

function init_ghost_state(log : seq<int>, mem : seq<int>, countdown : int) : GhostState
    requires |log| > 0;
    requires countdown >= 0;
    ensures ghost_state_inv(init_ghost_state(log, mem, countdown));
{
    GS(0, log[..], |mem|, mem[..], mem[..], mem[..], countdown, map[])
}

function mem_write(s : GhostState, off: int, val: int) : GhostState
    requires ghost_state_inv(s);
    requires 0 <= off < s.mem_len;
    ensures ghost_state_inv(mem_write(s, off, val));
    ensures mem_write(s, off, val).mem == s.mem[off := val];
    ensures mem_write(s, off, val).ideal_mem == s.ideal_mem[off := val];
    ensures mem_write(s, off, val).old_mem == s.old_mem;
    ensures mem_write(s, off, val).log == s.log;
    ensures mem_write(s, off, val).countdown == s.countdown;
    ensures mem_write(s, off, val).first_log_pos == s.first_log_pos;
    ensures mem_write(s, off, val).num_entry == s.num_entry;
{
    var new_mem := s.mem[off := val];
    var new_ideal_mem := s.ideal_mem[off := val];
    s.(mem := new_mem,
       ideal_mem := new_ideal_mem)
}

function log_write(s : GhostState, off : int, val: int) : GhostState
    requires ghost_state_inv(s);
    requires 0 <= off < |s.log|;
    ensures ghost_state_inv(log_write(s, off, val));
    ensures log_write(s, off, val).log == s.log[off := val];
    ensures log_write(s, off, val).mem == s.mem;
    ensures log_write(s, off, val).ideal_mem == s.ideal_mem;
    ensures log_write(s, off, val).old_mem == s.old_mem;
    ensures log_write(s, off, val).countdown == s.countdown;
    ensures log_write(s, off, val).first_log_pos == s.first_log_pos;
    ensures log_write(s, off, val).num_entry == s.num_entry;
{
     s.(log := s.log[off := val])
}

predicate valid_op(s : GhostState, op : GhostOp)
{
    match op
    case WriteMem(off, val) => 0 <= off < |s.mem|
    case WriteLog(off, val) => 0 <= off < |s.log|
}

function countdown (s : GhostState) : GhostState
{
    if s.countdown > 0 then
        s.(countdown := s.countdown - 1)
    else
        s
}

function normal_step (s : GhostState, op : GhostOp) : GhostState
    requires valid_op(s, op);
    requires ghost_state_inv(s);
    ensures ghost_state_inv(normal_step(s, op));
    ensures match op
        case WriteMem(off, val) => normal_step(s, op) == mem_write(s, off, val)
        case WriteLog(off, val) => normal_step(s, op) == log_write(s, off, val);
{
    match op
    case WriteMem(off, val) => mem_write(s, off, val)
    case WriteLog(off, val) => log_write(s, off, val)
}

function ghost_step (s : GhostState, op : GhostOp) : (GhostState, bool)
    requires valid_op(s, op);
    requires ghost_state_inv(s);
    ensures ghost_state_inv(normal_step(s, op));
    ensures ghost_step(s, op).1 ==> ghost_step(s, op).0.countdown == s.countdown - 1;
    ensures !ghost_step(s, op).1 ==> ghost_step(s, op).0 == s;
    ensures ghost_step(s, op).1 ==> ghost_step(s, op).0 == normal_step(s, op).(countdown := s.countdown - 1);
{
    if s.countdown > 0 then
        var s' := normal_step(s, op);
        (s'.(countdown := s.countdown - 1), true)
    else
        (s, false)
}

function mem_write_step (s : GhostState, off : int, val : int) : (GhostState, bool)
    requires 0 <= off < s.mem_len;
    requires ghost_state_inv(s);
    ensures mem_write_step(s, off, val).1 ==> mem_write_step(s, off, val).0.mem == s.mem[off := val];
    ensures mem_write_step(s, off, val).1 ==> mem_write_step(s, off, val).0.countdown == s.countdown - 1;
    ensures !mem_write_step(s, off, val).1 ==> mem_write_step(s, off, val).0 == s;
{
    ghost_step(s, WriteMem(off, val))
}

function log_write_step (s : GhostState, off : int, val : int) : (GhostState, bool)
    requires 0 <= off < |s.log|;
    requires ghost_state_inv(s);
    ensures log_write_step(s, off, val).1 ==> log_write_step(s, off, val).0.log == s.log[off := val];
    ensures log_write_step(s, off, val).1 ==> log_write_step(s, off, val).0.countdown == s.countdown - 1;
    ensures !log_write_step(s, off, val).1 ==> log_write_step(s, off, val).0 == s;
{
    ghost_step(s, WriteLog(off, val))
}

function set_num_entry (s : GhostState, n : int) : (GhostState, bool)
    requires 0 <= n * 2 < |s.log|;
    ensures set_num_entry(s, n).1 ==> set_num_entry(s, n).0.num_entry == n;
    ensures set_num_entry(s, n).1 ==> set_num_entry(s, n).0.countdown == s.countdown - 1;
    ensures set_num_entry(s, n).1 ==> set_num_entry(s, n).0.first_log_pos == s.first_log_pos;
    ensures set_num_entry(s, n).1 ==> set_num_entry(s, n).0.mem == s.mem;
    ensures set_num_entry(s, n).1 ==> set_num_entry(s, n).0.log == s.log;
    ensures set_num_entry(s, n).1 ==> set_num_entry(s, n).0.old_mem == s.old_mem;
    ensures set_num_entry(s, n).1 ==> set_num_entry(s, n).0.ideal_mem == s.ideal_mem;
    ensures !set_num_entry(s, n).1 ==> set_num_entry(s, n).0 == s;
{
    if s.countdown > 0 then
        (s.(num_entry := n,
            countdown := s.countdown - 1),
        true)
    else
        (s, false)
}

predicate crashed (s : GhostState)
{
    s.countdown <= 0
}

predicate old_mem_equiv (s : GhostState)
    requires ghost_state_inv(s);
{
    (forall o :: !(o in s.first_log_pos) && 0 <= o < |s.mem| ==> s.mem[o] == s.old_mem[o])
}

predicate ghost_tx_inv (s : GhostState)
{
    ghost_state_inv(s) &&
    (forall o :: o in s.first_log_pos ==> 0 <= o < s.mem_len) &&
    (forall o :: o in s.first_log_pos ==> 0 <= s.first_log_pos[o] < s.num_entry) &&
    (forall o :: o in s.first_log_pos ==> 0 <= s.first_log_pos[o] * 2 + 1 < |s.log|) &&
    (forall o :: o in s.first_log_pos ==> s.log[s.first_log_pos[o] * 2] == o) &&
    (forall o :: o in s.first_log_pos ==> s.log[s.first_log_pos[o] * 2 + 1] == s.old_mem[o]) &&
    (forall o :: o in s.first_log_pos ==> forall i :: 0 <= i < s.first_log_pos[o] ==> s.log[i * 2] != o) &&
    (forall i :: 0 <= i < s.num_entry ==> s.log[i * 2] in s.first_log_pos)
}

function ghost_begin_tx (s : GhostState) : GhostState
    requires ghost_state_inv(s);
    requires s.num_entry == 0;
    ensures ghost_state_inv(ghost_begin_tx(s));
    ensures ghost_tx_inv(ghost_begin_tx(s));
    ensures old_mem_equiv(ghost_begin_tx(s));
    ensures ghost_begin_tx(s).first_log_pos == map[];
    ensures ghost_begin_tx(s).old_mem == s.mem;
    ensures ghost_begin_tx(s).num_entry == 0;
{
    var (s', f) := set_num_entry(s, 0);
    var s' := s'.(first_log_pos := map[], old_mem := s.mem[..]);
    s'
}

function ghost_commit_tx (s : GhostState) : (GhostState, bool)
    requires ghost_tx_inv(s);
    requires old_mem_equiv(s);
    ensures ghost_state_inv(ghost_commit_tx(s).0);
    ensures ghost_tx_inv(ghost_commit_tx(s).0);
    ensures !ghost_commit_tx(s).1 ==> old_mem_equiv(ghost_commit_tx(s).0);
    ensures ghost_commit_tx(s).1 ==> ghost_commit_tx(s).0.num_entry == 0;
    ensures ghost_commit_tx(s).1 ==> ghost_commit_tx(s).0.first_log_pos == map[];
{
    var s' := s;
    var (s', f) := set_num_entry(s', 0);
    var s' := if f then s'.(first_log_pos := map[]) else s';
    (s', f)
}

function ghost_tx_write (s0 : GhostState, off : int, val : int) : GhostState
    requires ghost_tx_inv(s0);
    requires old_mem_equiv(s0);
    requires 0 <= off < s0.mem_len;
    requires 0 <= s0.num_entry * 2 + 2 < |s0.log|;
    ensures ghost_tx_inv(ghost_tx_write(s0, off, val));
    ensures old_mem_equiv(ghost_tx_write(s0, off, val));
    ensures |ghost_tx_write(s0, off, val).mem| == s0.mem_len;
    ensures !crashed(ghost_tx_write(s0, off, val)) ==> ghost_tx_write(s0, off, val).mem[off] == val;
    ensures ghost_tx_write(s0, off, val).first_log_pos == 
        if !(off in s0.first_log_pos) && s0.countdown > 0 && s0.countdown - 1 > 0 && s0.countdown - 2 > 0 && s0.countdown - 3 > 0 && s0.countdown - 4 > 0
        then s0.first_log_pos[off := s0.num_entry]
        else s0.first_log_pos;
{
    var s := s0;
    var log_idx := s.num_entry;
    var log_off := log_idx * 2;
    var old_val := s.mem[off];
    var (s, f) := log_write_step(s, log_off, off);
    var (s, f) := log_write_step(s, log_off + 1, old_val);
    var (s, f) := set_num_entry(s, log_idx + 1);
    var s := if f && !(off in s.first_log_pos)
             then s.(first_log_pos := s.first_log_pos[off := log_idx])
             else s;
    var (s, f) := mem_write_step(s, off, val);
    s
}

function reverse_recovery (s0 : GhostState, idx : int) : GhostState
    requires ghost_tx_inv(s0);
    requires old_mem_equiv(s0);
    requires 0 <= idx <= s0.num_entry;
    ensures ghost_tx_inv(reverse_recovery(s0, idx));
    ensures old_mem_equiv(reverse_recovery(s0, idx));
    ensures s0.old_mem == reverse_recovery(s0, idx).old_mem;
    ensures s0.first_log_pos == reverse_recovery(s0, idx).first_log_pos;
    ensures forall o :: o in s0.first_log_pos && s0.first_log_pos[o] >= idx ==>
                reverse_recovery(s0, idx).mem[o] == s0.mem[o];
    ensures forall o :: o in s0.first_log_pos && 0 <= s0.first_log_pos[o] < idx ==>
                reverse_recovery(s0, idx).mem[o] == s0.old_mem[o];
    decreases idx;
{
    if idx == 0 then
        s0
    else
        var s := s0;
        var i := idx - 1;
        var off := s.log[i * 2];
        var val := s.log[i * 2 + 1];
        var s := s.(mem := s.mem[off := val]);
        var s := reverse_recovery(s, idx - 1);
        s
}

function ghost_recover (s0 : GhostState) : GhostState
    requires ghost_tx_inv(s0);
    requires old_mem_equiv(s0);
    ensures ghost_recover(s0).mem == s0.old_mem;
    ensures ghost_recover(s0).num_entry == 0;
    ensures ghost_tx_inv(ghost_recover(s0));
    ensures old_mem_equiv(ghost_recover(s0));
{
    var s := reverse_recovery(s0, s0.num_entry);
    s.(num_entry := 0)
}


class UndoLog {
    var log_ : array<int>;
    var mem_ : array<int>;

    var impl_countdown : int;
    ghost var gs : GhostState;

    constructor () {}

    predicate ghost_state_equiv(gs : GhostState)
        reads this;
        reads mem_;
        reads log_;
    {
        log_.Length > 0 &&
        mem_[..] == gs.mem &&
        log_[1..] == gs.log &&
        log_[0] == gs.num_entry &&
        impl_countdown == gs.countdown
    }
    predicate state_inv()
        reads this;
        reads log_;
    {
        log_.Length > 1 && 0 <= log_[0] && (log_[0] * 2) < log_.Length
        && log_.Length < 0xffffffff && mem_ != log_
        && forall i : int :: 0 <= i < log_[0] ==> 0 <= log_[i * 2 + 1] < mem_.Length
        && impl_countdown >= 0
    }

    method init(log_size : int, mem_size : int, countdown : int)
        requires log_size > 1;
        requires mem_size > 0;
        requires log_size < 0xffffffff;
        modifies this;
        ensures fresh(log_);
        ensures fresh(mem_);
        ensures state_inv();
        ensures ghost_state_equiv(gs);
    {
        log_ := new int[log_size];
        mem_ := new int[mem_size];
        log_[0] := 0;

        impl_countdown := countdown;
        gs := GS(0, log_[1..], mem_size, mem_[..], mem_[..], mem_[..], countdown, map[]);
    }

    method impl_countdown_dec()
        modifies this;
        requires impl_countdown > 0;
        requires mem_ != log_;
        ensures mem_ != log_;
        ensures impl_countdown == old(impl_countdown) - 1;
        ensures impl_countdown >= 0;
        ensures gs == old(gs);
        ensures log_[..] == old(log_)[..];
        ensures mem_[..] == old(mem_)[..];
    {
        impl_countdown := impl_countdown - 1;
    }

    method write_mem(off : int, val : int)
        modifies this;
        modifies mem_;
        requires 0 <= off < mem_.Length;
        requires mem_ != log_;
        requires ghost_state_inv(gs);
        requires ghost_state_equiv(gs);
        requires 0 <= off < gs.mem_len;
        ensures mem_ == old(mem_);
        ensures log_ == old(log_);
        ensures gs == old(gs);
        ensures ghost_state_equiv(mem_write_step(gs, off, val).0);
    {
        if (impl_countdown > 0) {
            mem_[off] := val;
            impl_countdown := impl_countdown - 1;
        }
        // strongest post: mem_[off] == val if impl_countdown > 0, else unchanged
        // ghost_state_equiv(mem_write_step(gs, off, val).0) holds
    }

    method write_log(off : int, val : int)
        modifies this;
        modifies log_;
        requires 0 <= off <= |gs.log|;
        requires mem_ != log_;
        requires ghost_state_inv(gs);
        requires ghost_state_equiv(gs);
        requires off == 0 ==> 0 <= val * 2 < |gs.log|;
        ensures mem_ != log_;
        ensures mem_ == old(mem_);
        ensures log_ == old(log_);
        ensures log_.Length == old(log_).Length;
        ensures mem_[..] == old(mem_)[..];
        ensures log_[off] == val || log_[off] == old(log_)[off];
        ensures forall i :: 0 <= i < log_.Length && i != off ==> log_[i] == old(log_)[i];
        ensures gs == old(gs);
        ensures off > 0 ==> ghost_state_equiv(log_write_step(gs, off - 1, val).0);
        ensures off == 0 ==> ghost_state_equiv(set_num_entr
function abs(a: real) : real {if a>0.0 then a else -a}
