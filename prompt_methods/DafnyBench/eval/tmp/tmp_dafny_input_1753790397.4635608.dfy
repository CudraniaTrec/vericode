
/**
Consider cellular automata: a row of cells is repeatedly updated according to a rule. In this exercise I dabbled with,
each cell has the value either false or true. Each cell's next state depends only on the immediate neighbours, in the 
case where the cell is at the edges of the row, the inexistent neighbours are replaced by "false". The automaton table 
will contain the initial row, plus a row for each number of steps.
 */
class Automaton {

/**
This method computes the automaton.
Provide the initial row: init, the rule and the desired number of steps
 */
method ExecuteAutomaton(init: seq<bool>, rule: (bool, bool, bool) -> bool, steps: nat)
  returns (table: seq<seq<bool>>)
  // we need the initial row to have the length bigger or equal to two
  requires |init| >= 2
  // after computation the automaton is made of the initial row plus a row for each of the steps
  ensures |table| == 1 + steps
  // the automaton must have the initial row at the top
  ensures table[0] == init;
  // all rows in the automaton must be the same length
  ensures forall i | 0 <= i < |table| :: |table[i]| == |init|
  // all the middle row elements (with existing neighbours) after a step, will be equal to the rule applied on the element in the previous state
  // and its neigbours
  ensures forall i | 0 <= i < |table| - 1 ::
            forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
  // the corner row elements (with non-existing neighbours) after a step, will be equal to the rule applied on the element in the previous state,
  // its neighbour and false
  ensures forall i | 0 <= i < |table| - 1 ::
            table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
{
  // the table containing the automaton 
  var result : seq<seq<bool>> := [init];
  // the current row
  var currentSeq := init;
  var index := 0;

  while index < steps
    invariant 0 <= index <= steps
    invariant |result| == 1 + index
    invariant result[0] == init
    invariant forall i :: 0 <= i < |result| ==> |result[i]| == |init|
    invariant currentSeq == result[index]
    invariant forall i :: 0 <= i < index ==>
      forall j :: 1 <= j <= |result[i]| - 2 ==>
        result[i + 1][j] == rule(result[i][j - 1], result[i][j], result[i][j + 1])
    invariant forall i :: 0 <= i < index ==>
      result[i + 1][0] == rule(false, result[i][0], result[i][1]) &&
      result[i + 1][|result[i]| - 1] == rule(result[i][|result[i]| - 2], result[i][|result[i]| - 1], false)
    decreases steps - index
  {
    var index2 := 1;
    // the next row to be computed
    var nextSeq := [];
    nextSeq := nextSeq + [rule(false, currentSeq[0], currentSeq[1])];

    while index2 < |currentSeq| - 1
      invariant 1 <= index2 <= |currentSeq| - 1
      invariant |nextSeq| == index2
      invariant forall k :: 0 <= k < index2 ==>
        nextSeq[k] == (if k == 0 then rule(false, currentSeq[0], currentSeq[1])
                       else rule(currentSeq[k - 1], currentSeq[k], currentSeq[k + 1]))
      decreases |currentSeq| - 1 - index2
    {
      nextSeq := nextSeq + [rule(currentSeq[index2 - 1], currentSeq[index2], currentSeq[index2 + 1])];
      index2 := index2 + 1;
    }
    nextSeq := nextSeq + [rule(currentSeq[|currentSeq| - 2], currentSeq[|currentSeq| - 1], false)];
    assert |nextSeq| == |currentSeq|;
    assert forall j :: 1 <= j <= |currentSeq| - 2 ==>
      nextSeq[j] == rule(currentSeq[j - 1], currentSeq[j], currentSeq[j + 1]);
    assert nextSeq[0] == rule(false, currentSeq[0], currentSeq[1]);
    assert nextSeq[|currentSeq| - 1] == rule(currentSeq[|currentSeq| - 2], currentSeq[|currentSeq| - 1], false);

    currentSeq := nextSeq;
    result := result + [nextSeq];
    index := index + 1;
  }

  return result;
}

// example rule
function TheRule(a: bool, b: bool, c: bool) : bool
{
  a || b || c
}

// example rule 2
function TheRule2(a: bool, b: bool, c: bool) : bool
{
  a && b && c
}

method testMethod() {
  // the initial row
  var init := [false, false, true, false, false];

  // calculate automaton steps with 
  var result := ExecuteAutomaton(init, TheRule, 3);
  // the intial row plus the three steps of the automaton are showed bellow

  var result2 := ExecuteAutomaton(init, TheRule2, 2);
  // the intial row plus the two steps of the automaton are showed bellow
}
}

function abs(a: real) : real {if a>0.0 then a else -a}
