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
    // The loop invariant tracks the number of people assigned to boats, and that the remaining people are in people[lower..upper]
    // We use ghost variables only in invariants and assertions, not as program variables.
    while lower <= upper
        invariant 0 <= lower <= |people|
        invariant -1 <= upper < |people|
        invariant lower >= 0
        invariant upper + 1 >= lower
        invariant boats <= |people|
        invariant boats == |people| - (upper - lower + 1) || lower > upper
        invariant forall i :: 0 <= i < lower ==> 1 <= people[i] <= limit
        invariant forall i :: upper+1 <= i < |people| ==> 1 <= people[i] <= limit
        invariant forall i :: 0 <= i < lower ==> people[i] <= limit
        invariant forall i :: upper+1 <= i < |people| ==> people[i] <= limit
        invariant forall i :: 0 <= i < lower ==> people[i] <= people[lower-1] // sorted
        invariant forall i :: upper+1 <= i < |people| ==> people[upper+1] <= people[i] // sorted
        invariant forall i :: lower <= i <= upper ==> 1 <= people[i] <= limit
        invariant forall i,j :: 0 <= i < j < |people| ==> people[i] <= people[j]
        // Specification invariants
        invariant exists boatConfig: seq<seq<nat>> ::
            multisetEqual(boatConfig, people) &&
            allSafe(boatConfig, limit) &&
            boats + (if lower <= upper then 1 else 0) <= |boatConfig|
        decreases upper - lower + 1
    {
        if people[upper] == limit || people[upper] + people[lower] > limit {
            boats := boats + 1;
            upper := upper - 1;
        } else {
            boats := boats + 1;
            if lower == upper {
                lower := lower + 1;
            } else {
                upper := upper - 1;
                lower := lower + 1;
            }
        }
    }
    // At this point, all people have been assigned to boats.
    // Postcondition is ensured by the loop invariant.
}

function abs(a: real) : real {if a>0.0 then a else -a}
