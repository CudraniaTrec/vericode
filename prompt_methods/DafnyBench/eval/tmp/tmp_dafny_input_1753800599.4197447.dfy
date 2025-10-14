
function sumBoat(s: seq<nat>): nat 
    requires 1 <= |s| <= 2
{
    if |s| == 1 then s[0] else s[0] + s[1]
}

predicate isSafeBoat(boat: seq<nat>, limit: nat) {
    1 <= |boat| <= 2 && sumBoat(boat) <= limit
}

function multisetAdd(ss: seq<seq<nat>>): multiset<nat> {
    if ss == [] then multiset{} else multiset(ss[0]) + multisetAdd(ss[1..])
}

predicate multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>) {
    multiset(xs) == multisetAdd(ss)
}

predicate allSafe(boats: seq<seq<nat>>, limit: nat) {
    forall boat :: boat in boats ==> isSafeBoat(boat, limit)
}

predicate sorted(list: seq<int>)
{
    forall i,j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|
{
    boats := 0;
    var lower: nat := 0;
    var upper: int := |people| - 1;
    ghost var visitedUpper: multiset<nat> := multiset{};
    ghost var visitedLower: multiset<nat> := multiset{};
    ghost var safeBoats: seq<seq<nat>> := [];
    while lower <= upper 
        invariant 0 <= lower <= |people|
        invariant -1 <= upper < |people|
        invariant lower >= 0
        invariant upper + 1 >= lower
        invariant boats == |safeBoats|
        invariant visitedUpper + visitedLower == multiset(people[lower..upper+1]) == multiset(people) - multiset(people[lower..upper+1])
        invariant multisetAdd(safeBoats) == multiset(people) - multiset(people[lower..upper+1])
        invariant allSafe(safeBoats, limit)
        invariant forall i :: 0 <= i < lower ==> people[i] in visitedLower
        invariant forall i :: upper+1 <= i < |people| ==> people[i] in visitedUpper
        invariant forall i :: lower <= i <= upper ==> !(people[i] in visitedLower) && !(people[i] in visitedUpper)
        decreases upper - lower + 1
    {
        if people[upper] == limit || people[upper] + people[lower] > limit {
            assert 1 <= people[upper] <= limit;
            boats := boats + 1;
            safeBoats := [[people[upper]]] + safeBoats;
            visitedUpper := visitedUpper + multiset{people[upper]};
            upper := upper - 1;
        } else {
            boats := boats + 1;
            if lower == upper {
                assert 1 <= people[lower] <= limit;
                visitedLower := visitedLower + multiset{people[lower]};
                safeBoats := [[people[lower]]] + safeBoats;
            } else {
                assert people[upper] + people[lower] <= limit;
                assert 1 <= people[upper] <= limit && 1 <= people[lower] <= limit;
                visitedUpper := visitedUpper + multiset{people[upper]};
                visitedLower := visitedLower + multiset{people[lower]};
                safeBoats := [[people[upper], people[lower]]] + safeBoats;
                upper := upper - 1;
            }
            lower := lower + 1;
        }
    }
    assert multisetAdd(safeBoats) == multiset(people);
    assert allSafe(safeBoats, limit);
    boats := |safeBoats|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
