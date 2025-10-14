
// include "IOModel.i.dfy"
// include "../lib/DataStructures/LinearMutableMap.i.dfy"

module CommitterCommitModel {
  import opened NativeTypes
  import opened Options

  import opened DiskLayout
  import opened InterpretationDiskOps
  import opened ViewOp
  import JC = JournalCache
  import opened Journal
  import opened JournalBytes
  import opened DiskOpModel
  import SectorType

  import LinearMutableMap
  // import opened StateModel
  import opened IOModel

  function SyncReqs2to1Iterate(
      m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>,
      it: LinearMutableMap.Iterator<JC.SyncReqStatus>,
      m0: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
    : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires LinearMutableMap.Inv(m)
  requires LinearMutableMap.WFIter(m, it)
  requires LinearMutableMap.Inv(m0)
  requires m0.contents.Keys == it.s
  ensures LinearMutableMap.Inv(m')
  decreases it.decreaser
  {
    if it.next.Done? then
      m0
    else (
      LinearMutableMap.LemmaIterIndexLtCount(m, it);
      LinearMutableMap.CountBound(m);
      SyncReqs2to1Iterate(
        m,
        LinearMutableMap.IterInc(m, it),
        LinearMutableMap.Insert(m0, it.next.key,
            (if it.next.value == JC.State2 then JC.State1 else it.next.value))
      )
    )
  }

  function {:opaque} SyncReqs2to1(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
      : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires LinearMutableMap.Inv(m)
  ensures LinearMutableMap.Inv(m')
  {
    SyncReqs2to1Iterate(m,
      LinearMutableMap.IterStart(m),
      LinearMutableMap.Constructor(128))
  }

  lemma SyncReqs2to1Correct(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires LinearMutableMap.Inv(m)
  ensures SyncReqs2to1(m).contents == JC.syncReqs2to1(m.contents)
  {
    reveal_SyncReqs2to1();
    var it := LinearMutableMap.IterStart(m);
    var m0 := LinearMutableMap.Constructor(128);
    while !it.next.Done?
      invariant LinearMutableMap.Inv(m)
      invariant LinearMutableMap.WFIter(m, it)
      invariant LinearMutableMap.Inv(m0)
      invariant m0.contents.Keys == it.s
      invariant forall id | id in it.s ::
          m0.contents[id] == (if m.contents[id] == JC.State2 then JC.State1 else m.contents[id])
      invariant SyncReqs2to1(m) == SyncReqs2to1Iterate(m, it, m0)
      decreases it.decreaser
    {
      LinearMutableMap.LemmaIterIndexLtCount(m, it);
      LinearMutableMap.CountBound(m);
      m0 := LinearMutableMap.Insert(m0, it.next.key,
          (if it.next.value == JC.State2 then JC.State1 else it.next.value));
      it := LinearMutableMap.IterInc(m, it);
    }
    assert SyncReqs2to1(m).contents == JC.syncReqs2to1(m.contents);
  }

  function SyncReqs3to2Iterate(
      m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>,
      it: LinearMutableMap.Iterator<JC.SyncReqStatus>,
      m0: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
    : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires LinearMutableMap.Inv(m)
  requires LinearMutableMap.WFIter(m, it)
  requires LinearMutableMap.Inv(m0)
  requires m0.contents.Keys == it.s
  ensures LinearMutableMap.Inv(m')
  decreases it.decreaser
  {
    if it.next.Done? then
      m0
    else (
      LinearMutableMap.LemmaIterIndexLtCount(m, it);
      LinearMutableMap.CountBound(m);
      SyncReqs3to2Iterate(
        m,
        LinearMutableMap.IterInc(m, it),
        LinearMutableMap.Insert(m0, it.next.key,
            (if it.next.value == JC.State3 then JC.State2 else it.next.value))
      )
    )
  }

  function {:opaque} SyncReqs3to2(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
      : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires LinearMutableMap.Inv(m)
  ensures LinearMutableMap.Inv(m')
  {
    SyncReqs3to2Iterate(m,
      LinearMutableMap.IterStart(m),
      LinearMutableMap.Constructor(128))
  }

  lemma SyncReqs3to2Correct(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
  requires LinearMutableMap.Inv(m)
  ensures SyncReqs3to2(m).contents == JC.syncReqs3to2(m.contents)
  {
    reveal_SyncReqs3to2();
    var it := LinearMutableMap.IterStart(m);
    var m0 := LinearMutableMap.Constructor(128);
    while !it.next.Done?
      invariant LinearMutableMap.Inv(m)
      invariant LinearMutableMap.WFIter(m, it)
      invariant LinearMutableMap.Inv(m0)
      invariant m0.contents.Keys == it.s
      invariant forall id | id in it.s ::
          m0.contents[id] == (if m.contents[id] == JC.State3 then JC.State2 else m.contents[id])
      invariant SyncReqs3to2(m) == SyncReqs3to2Iterate(m, it, m0)
      decreases it.decreaser
    {
      LinearMutableMap.LemmaIterIndexLtCount(m, it);
      LinearMutableMap.CountBound(m);
      m0 := LinearMutableMap.Insert(m0, it.next.key,
          (if it.next.value == JC.State3 then JC.State2 else it.next.value));
      it := LinearMutableMap.IterInc(m, it);
    }
    assert SyncReqs3to2(m).contents == JC.syncReqs3to2(m.contents);
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
