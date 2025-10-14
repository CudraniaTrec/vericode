class Heap {
  var arr: array<int>

  constructor Heap (input: array<int>)
   ensures this.arr == input {
     this.arr := input;
  }

  function parent(idx: int): int
  {
    if idx == 0 then -1
    else if idx % 2 == 0 then (idx-2)/2
    else (idx-1)/2
  }

  predicate IsMaxHeap(input: seq<int>)
  {
    forall i :: 0 <= i < |input| ==>
      && (2*i+1 < |input| ==> input[i] >= input[2*i+1])
      && (2*i+2 < |input| ==> input[i] >= input[2*i+2])
  }

  predicate IsAlmostMaxHeap(input: seq<int>, idx: int)
    requires 0 <= idx
  {
    && (forall i :: 0 <= i < |input| ==>
        && (2*i+1 < |input| && i != idx ==> input[i] >= input[2*i+1])
        && (2*i+2 < |input| && i != idx ==> input[i] >= input[2*i+2]))
    && (0 <= parent(idx) < |input| && 2*idx+1 < |input| ==> input[parent(idx)] >= input[2*idx+1])
    && (0 <= parent(idx) < |input| && 2*idx+2 < |input| ==> input[parent(idx)] >= input[2*idx+2])
  }

  method heapify(idx: int)
    returns (nidx: int)
    modifies this, this.arr
    requires 0 <= idx < this.arr.Length
    requires IsAlmostMaxHeap(this.arr[..], idx)
    ensures nidx == -1 || idx < nidx < this.arr.Length
    ensures nidx == -1 ==> IsMaxHeap(this.arr[..])
    ensures idx < nidx < this.arr.Length ==> IsAlmostMaxHeap(this.arr[..], nidx)
  {
    if (2*idx+1 >= this.arr.Length) && (2*idx+2 >= this.arr.Length) {
      nidx := -1;
      return;
    }
    else {
      nidx := idx;
      // strongest possible: nidx is always idx, 2*idx+1, or 2*idx+2
      assert nidx == idx;
      if 2*idx+1 < this.arr.Length && this.arr[nidx] < this.arr[2*idx+1] {
        nidx := 2*idx+1;
        assert nidx == 2*idx+1;
      }
      if 2*idx+2 < this.arr.Length && this.arr[nidx] < this.arr[2*idx+2] {
        nidx := 2*idx+2;
        assert nidx == 2*idx+2;
      }
      assert nidx == idx || nidx == 2*idx+1 || nidx == 2*idx+2;
      if nidx == idx {
        nidx := -1;
        // All heap properties are satisfied, so IsMaxHeap holds
        assert IsMaxHeap(this.arr[..]);
        return;
      }
      else {
        // Swap arr[idx] and arr[nidx]
        var oldArr := this.arr[..];
        this.arr[idx], this.arr[nidx] := this.arr[nidx], this.arr[idx];

        // Strongest possible assertions about the new array:
        // - All heap properties except possibly at nidx are preserved
        // - At nidx, the "almost" heap property holds
        assert forall i :: 0 <= i < this.arr.Length ==>
          ((2*i+1 < this.arr.Length && i != nidx) ==> this.arr[i] >= this.arr[2*i+1]);
        assert forall i :: 0 <= i < this.arr.Length ==>
          ((2*i+2 < this.arr.Length && i != nidx) ==> this.arr[i] >= this.arr[2*i+2]);
        assert (0 <= parent(nidx) < this.arr.Length && 2*nidx+1 < this.arr.Length ==> this.arr[parent(nidx)] >= this.arr[2*nidx+1]);
        assert (0 <= parent(nidx) < this.arr.Length && 2*nidx+2 < this.arr.Length ==> this.arr[parent(nidx)] >= this.arr[2*nidx+2]);
        assert IsAlmostMaxHeap(this.arr[..], nidx);
      }
    }
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
