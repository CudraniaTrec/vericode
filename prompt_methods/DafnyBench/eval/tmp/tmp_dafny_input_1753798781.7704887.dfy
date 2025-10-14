// include "IOModel.i.dfy"
// include "../lib/DataStructures/LinearMutableMap.i.dfy"

module CommitterCommitModel {
  import opened LinearMutableMap
  import JC = JournalCache

  function SyncReqs2to1Iterate(
      m: LinearHashMap<JC.SyncReqStatus>,
      it: Iterator<JC.SyncReqStatus>,
      m0: LinearHashMap<JC.SyncReqStatus>)
    : (m' : LinearHashMap<JC.SyncReqStatus>)
  requires Inv(m)
  requires WFIter(m, it)
  requires Inv(m0)
  requires m0.contents.Keys == it.s
  ensures Inv(m')
  decreases it.decreaser
  {
    if it.next.Done? then
      m0
    else (
      LemmaIterIndexLtCount(m, it);
      CountBound(m);
      SyncReqs2to1Iterate(
        m,
        IterInc(m, it),
        Insert(m0, it.next.key,
            (if it.next.value == JC.State2 then JC.State1 else it.next.value))
      )
    )
  }

  function {:opaque} SyncReqs2to1(m: LinearHashMap<JC.SyncReqStatus>)
      : (m' : LinearHashMap<JC.SyncReqStatus>)
  requires Inv(m)
  ensures Inv(m')
  {
    SyncReqs2to1Iterate(m,
      IterStart(m),
      Constructor(128))
  }

  lemma SyncReqs2to1Correct(m: LinearHashMap<JC.SyncReqStatus>)
  requires Inv(m)
  ensures SyncReqs2to1(m).contents == JC.syncReqs2to1(m.contents)
  {
    reveal_SyncReqs2to1();
    var it := IterStart(m);
    var m0 := Constructor(128);
    while !it.next.Done?
      invariant Inv(m)
      invariant WFIter(m, it)
      invariant Inv(m0)
      invariant m0.contents.Keys == it.s
      invariant forall id | id in it.s ::
          m0.contents[id] == (if m.contents[id] == JC.State2 then JC.State1 else m.contents[id])
      invariant SyncReqs2to1(m) == SyncReqs2to1Iterate(m, it, m0)
      decreases it.decreaser
    {
      LemmaIterIndexLtCount(m, it);
      CountBound(m);
      m0 := Insert(m0, it.next.key,
          (if it.next.value == JC.State2 then JC.State1 else it.next.value));
      it := IterInc(m, it);
    }
    assert SyncReqs2to1(m).contents == JC.syncReqs2to1(m.contents);
  }

  function SyncReqs3to2Iterate(
      m: LinearHashMap<JC.SyncReqStatus>,
      it: Iterator<JC.SyncReqStatus>,
      m0: LinearHashMap<JC.SyncReqStatus>)
    : (m' : LinearHashMap<JC.SyncReqStatus>)
  requires Inv(m)
  requires WFIter(m, it)
  requires Inv(m0)
  requires m0.contents.Keys == it.s
  ensures Inv(m')
  decreases it.decreaser
  {
    if it.next.Done? then
      m0
    else (
      LemmaIterIndexLtCount(m, it);
      CountBound(m);
      SyncReqs3to2Iterate(
        m,
        IterInc(m, it),
        Insert(m0, it.next.key,
            (if it.next.value == JC.State3 then JC.State2 else it.next.value))
      )
    )
  }

  function {:opaque} SyncReqs3to2(m: LinearHashMap<JC.SyncReqStatus>)
      : (m' : LinearHashMap<JC.SyncReqStatus>)
  requires Inv(m)
  ensures Inv(m')
  {
    SyncReqs3to2Iterate(m,
      IterStart(m),
      Constructor(128))
  }

  lemma SyncReqs3to2Correct(m: LinearHashMap<JC.SyncReqStatus>)
  requires Inv(m)
  ensures SyncReqs3to2(m).contents == JC.syncReqs3to2(m.contents)
  {
    reveal_SyncReqs3to2();
    var it := IterStart(m);
    var m0 := Constructor(128);
    while !it.next.Done?
      invariant Inv(m)
      invariant WFIter(m, it)
      invariant Inv(m0)
      invariant m0.contents.Keys == it.s
      invariant forall id | id in it.s ::
          m0.contents[id] == (if m.contents[id] == JC.State3 then JC.State2 else m.contents[id])
      invariant SyncReqs3to2(m) == SyncReqs3to2Iterate(m, it, m0)
      decreases it.decreaser
    {
      LemmaIterIndexLtCount(m, it);
      CountBound(m);
      m0 := Insert(m0, it.next.key,
          (if it.next.value == JC.State3 then JC.State2 else it.next.value));
      it := IterInc(m, it);
    }
    assert SyncReqs3to2(m).contents == JC.syncReqs3to2(m.contents);
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
