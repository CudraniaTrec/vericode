module ModelingTM {
    type ProcessId = nat
    type MemoryObject = nat
    type TimeStamp = nat

    class Operation {
        const isWrite: bool
        const memObject: MemoryObject
    }

    class Transaction {
        const ops: seq<Operation>
    }

    // Process state : transaction progress and process memory.
    class ProcessState {
        const currentTx: nat
        const currentOp: int
        const currentSubOp: nat
        const readSet: map<MemoryObject, TimeStamp>
        const writeSet: set<MemoryObject>

        constructor () {
            currentTx := 0;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor nextSubOp(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp
            ensures this.currentSubOp == that.currentSubOp + 1
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp + 1;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor nextOp(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp + 1
            ensures this.currentSubOp == 0
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp + 1;
            currentSubOp := 0;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor abortTx(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == -1
            ensures this.currentSubOp == 0
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := -1;
            currentSubOp := 0;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor restartTx(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == 0
            ensures this.currentSubOp == 0
            ensures this.readSet == map[]
            ensures this.writeSet == {}
        {
            currentTx := that.currentTx;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor nextTx(that: ProcessState)
            ensures this.currentTx == that.currentTx + 1
            ensures this.currentOp == 0
            ensures this.currentSubOp == 0
            ensures this.readSet == map[]
            ensures this.writeSet == {}
        {
            currentTx := that.currentTx + 1;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor addToReadSet(that: ProcessState, obj: MemoryObject, ts: TimeStamp)
            ensures currentTx == that.currentTx
            ensures currentOp == that.currentOp
            ensures currentSubOp == that.currentSubOp
            ensures readSet.Keys == that.readSet.Keys + {obj}
                && readSet[obj] == ts
                && forall o :: o in readSet && o != obj ==> readSet[o] == that.readSet[o]
            ensures writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp;
            readSet := that.readSet[obj := ts];
            writeSet := that.writeSet;
        }

        constructor addToWriteSet(that: ProcessState, obj: MemoryObject)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp
            ensures this.currentSubOp == that.currentSubOp
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet + {obj}
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp;
            readSet := that.readSet;
            writeSet := that.writeSet + {obj};
        }
    }

    class TMSystem {
        const txQueues : map<ProcessId, seq<Transaction>>
        const procStates : map<ProcessId, ProcessState>
        const dirtyObjs: set<MemoryObject>
        const lockedObjs: set<MemoryObject>
        const objTimeStamps: map<MemoryObject, nat>

        constructor (q: map<ProcessId, seq<Transaction>>) {
            txQueues := q;
            procStates := map[];
            dirtyObjs := {};
            lockedObjs := {};
            objTimeStamps := map[];
        }

        constructor initTimestamp(that: TMSystem, obj: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps.Keys ==  that.objTimeStamps.Keys + {obj}
                && objTimeStamps[obj] == 0
                && forall o :: o in objTimeStamps && o != obj ==> objTimeStamps[o] == that.objTimeStamps[o]
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps[obj := 0];
        }
        
        constructor updateState(that: TMSystem, pid: ProcessId, state: ProcessState)
            ensures txQueues == that.txQueues
            ensures procStates.Keys == that.procStates.Keys + {pid}
                && procStates[pid] == state
                && forall p :: p in procStates && p != pid ==> procStates[p] == that.procStates[p]
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates[pid := state];
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }
        
        constructor markDirty(that: TMSystem, obj: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs + {obj}
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs + {obj};
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }
        
        constructor clearDirty(that: TMSystem, writeSet: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs - writeSet
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs - writeSet;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }

        constructor acquireLock(that: TMSystem, o: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs + {o}
            ensures objTimeStamps == that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs + {o};
            objTimeStamps := that.objTimeStamps;
        }

        constructor releaseLocks(that: TMSystem, objs: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs - objs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs - objs;
            objTimeStamps := that.objTimeStamps;
        }
        
        constructor updateTimestamps(that: TMSystem, objs: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps.Keys == that.objTimeStamps.Keys
                && forall o :: o in that.objTimeStamps ==>
                if(o in objs) then objTimeStamps[o] != that.objTimeStamps[o] else objTimeStamps[o] == that.objTimeStamps[o]
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := map o | o in that.objTimeStamps ::
                if(o in objs) then (that.objTimeStamps[o] + 1) else that.objTimeStamps[o];
        }

        predicate stateValid(pid: ProcessId, state: ProcessState)
            requires pid in procStates && state == procStates[pid]
        {
            pid in txQueues &&
            state.currentTx <= |txQueues[pid]| &&
            (
                (state.currentTx == |txQueues[pid]| &&
                    state.currentOp == 0 &&
                    state.currentSubOp == 0 &&
                    |state.readSet| == 0 &&
                    |state.writeSet| == 0
                ) ||
                (state.currentTx < |txQueues[pid]| &&
                    var tx := txQueues[pid][state.currentTx];
                    state.currentOp <= |tx.ops| &&
                    state.currentOp >= -1 &&
                    (
                        (state.currentOp >= 0 && state.currentOp < |tx.ops| && state.currentSubOp < 2) ||
                        (state.currentOp == |tx.ops| && state.currentSubOp < 4) ||
                        (state.currentOp == -1 && state.currentSubOp < 3)
                    ) &&
                    state.readSet.Keys <= objTimeStamps.Keys &&
                    state.writeSet <= lockedObjs
                )
            )
        }

        predicate validSystem()
        {
            procStates.Keys <= txQueues.Keys &&
            dirtyObjs <= objTimeStamps.Keys &&
            lockedObjs <= objTimeStamps.Keys &&
            forall p :: p in procStates ==> stateValid(p, procStates[p])
        }
    }
    

    method Step(input: TMSystem, pid: ProcessId) returns (system: TMSystem)
        requires pid in input.txQueues
        requires pid in input.procStates
        requires input.validSystem()
        ensures system.validSystem()
    {
        system := input;
        var state: ProcessState := system.procStates[pid];
        var txs := system.txQueues[pid];

        if (state.currentTx >= |txs|) {
            // Nothing left to do.
            // The only valid state for a finished process is:
            //   state.currentOp == 0, state.currentSubOp == 0, |state.readSet| == 0, |state.writeSet| == 0
            //   (see stateValid)
            // So, system remains unchanged and is valid.
            assert state.currentOp == 0;
            assert state.currentSubOp == 0;
            assert |state.readSet| == 0;
            assert |state.writeSet| == 0;
            assert system.validSystem();
            return;
        }
        var tx := txs[state.currentTx];

        if (state.currentOp == |tx.ops|) {
            // tryCommit
            if(state.currentSubOp == 0) {
                if !(forall o :: o in state.readSet ==> o in state.writeSet || o !in system.lockedObjs) {
                    state := new ProcessState.abortTx(state);
                    system := new TMSystem.updateState(system, pid, state);
                    return;
                }
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 1) {
                if !(forall o :: o in state.readSet ==> state.readSet[o] == system.objTimeStamps[o]) {
                    state := new ProcessState.abortTx(state);
                    system := new TMSystem.updateState(system, pid, state);
                    return;
                }
                system := new TMSystem.clearDirty(system, state.writeSet);
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 2) {
                system := new TMSystem.updateTimestamps(system, state.writeSet);
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 3) {
                system := new TMSystem.releaseLocks(system, state.writeSet);
                state := new ProcessState.nextTx(state);
            } else {
            }
        } else if (state.currentOp == -1) {
            // Abort
            if(state.currentSubOp == 0) {
                system := new TMSystem.clearDirty(system, state.writeSet);
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 1) {
                system := new TMSystem.updateTimestamps(system, state.writeSet);
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 2) {
                system := new TMSystem.releaseLocks(system, state.writeSet);
                state := new ProcessState.restartTx(state);
            } else {
            }
        } else if (state.currentOp >= 0 && state.currentOp < |tx.ops|) {
            var op := tx.ops[state.currentOp];
            var o := op.memObject;
            if(o !in system.objTimeStamps) {
                system := new TMSystem.initTimestamp(system, o);
            }
            if(op.isWrite) {
                if(state.currentSubOp == 0) {
                    if(!(op.memObject in state.writeSet)) {
                        if(o in system.lockedObjs) {
                            state := new ProcessState.abortTx(state);
                        } else {
                            system := new TMSystem.acquireLock(system, o);
                            state := new ProcessState.addToWriteSet(state, o);
                            state := new ProcessState.nextSubOp(state);
                        }
                    } else {
                        state := new ProcessState.nextSubOp(state);
                    }
                } else if (state.currentSubOp == 1) {
                    system := new TMSystem.markDirty(system, o);
                    state := new ProcessState.nextOp(state);
                } else {
                }
            } else {
                if(state.currentSubOp == 0) {
                    if(o in state.writeSet || o in state.readSet) {
                        state := new ProcessState.nextOp(state);
                    } else {
                        state := new ProcessState.addToReadSet(state, o, system.objTimeStamps[o]);
                        state := new ProcessState.nextSubOp(state);
                    }
                } else if (state.currentSubOp == 1) {
                    if(o in system.lockedObjs) {
                        state := new ProcessState.abortTx(state);
                    } else {
                        state := new ProcessState.nextOp(state);
                    }
                } else {
                }
            }
        } else {
        }
        system := new TMSystem.updateState(system, pid, state);
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
