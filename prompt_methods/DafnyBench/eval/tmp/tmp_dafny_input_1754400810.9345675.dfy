
/* https://leetcode.com/problems/longest-palindromic-substring/
Given a string s, return the longest palindromic substring in s.

Example 1:
Input: s = "babad"
Output: "bab"
Explanation: "aba" is also a valid answer.
*/


// Specifying the problem: whether `s[i..j]` is palindromic
ghost predicate palindromic(s: string, i: int, j: int)
  requires 0 <= i <= j <= |s|
{
  j - i < 2 || (s[i] == s[j-1] && palindromic(s, i+1, j-1))
}

// A "common sense" about palindromes:
lemma lemma_palindromic_contains(s: string, lo: int, hi: int, lo': int, hi': int)
  requires 0 <= lo <= lo' <= hi' <= hi <= |s|
  requires lo + hi == lo' + hi'
  requires palindromic(s, lo, hi)
  ensures palindromic(s, lo', hi')
{
  if lo < lo' {
    lemma_palindromic_contains(s, lo + 1, hi - 1, lo', hi');
  }
}

// A useful "helper function" that returns the longest palindrome at a given center (i0, j0).
method expand_from_center(s: string, i0: int, j0: int) returns (lo: int, hi: int)
  requires 0 <= i0 <= j0 <= |s|
  requires palindromic(s, i0, j0)
  ensures 0 <= lo <= hi <= |s| && palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j)  // Among all palindromes
    && i + j == i0 + j0                                             // sharing the same center,
    :: j - i <= hi - lo                                             // `s[lo..hi]` is longest.
{
  lo, hi := i0, j0;

  // we try expanding whenever possible:
  while lo - 1 >= 0 && hi < |s| && s[lo - 1] == s[hi]
    invariant 0 <= lo <= hi <= |s|
    invariant i0 + j0 == lo + hi
    invariant palindromic(s, lo, hi)
    invariant forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == i0 + j0 && (i < lo || j > hi) :: j - i <= hi - lo
  {
    lo, hi := lo - 1, hi + 1;
  }

  // proves that we cannot go further:
  forall i, j | 0 <= i <= j <= |s| && i + j == i0 + j0 && j - i > hi - lo ensures !palindromic(s, i, j) {
    if palindromic(s, i, j) { // prove by contradiction:
      lemma_palindromic_contains(s, i, j, lo - 1, hi + 1);
    }
  }
}


// The main algorithm.
// We traverse all centers from left to right, and "expand" each of them, to find the longest palindrome.
method longestPalindrome(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]  // `ans` is indeed a substring in `s`
  ensures palindromic(s, lo, hi)  // `ans` is palindromic
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo  // `ans` is longest
{
  lo, hi := 0, 0;
  var n := |s|;
  for k := 0 to n
    invariant 0 <= lo <= hi <= n
    invariant forall i, j | 0 <= i <= j <= n && palindromic(s, i, j) && i + j < 2 * k :: j - i <= hi - lo
    invariant palindromic(s, lo, hi)
  {
    var a, b := expand_from_center(s, k, k);
    if b - a > hi - lo {
      lo, hi := a, b;
    }
    var c, d := expand_from_center(s, k, k + 1);
    if d - c > hi - lo {
      lo, hi := c, d;
    }
  }
  return s[lo..hi], lo, hi;
}


/* Discussions
1. Dafny is super bad at slicing (esp. nested slicing).
  Do circumvent it whenever possible. It can save you a lot of assertions & lemmas!

  For example, instead of `palindromic(s[i..j])`, use the pattern `palindromic(s, i, j)` instead.
  I didn't realize this (ref: https://github.com/Nangos/dafleet/commit/3302ddd7642240ff2b2f6a8c51e8becd5c9b6437),
  Resulting in a couple of clumsy lemmas.

2. Bonus -- Manacher's algorithm
  Our above solution needs `O(|s|^2)` time in the worst case. Can we improve it? Yes.

  Manacher's algorithm guarantees an `O(|s|)` time.
  To get the intuition, ask yourself: when will it really take `O(|s|^2)` time?
  When there are a lot of "nesting and overlapping" palindromes. like in `abcbcbcba` or even `aaaaaa`.

  Imagine each palindrome as a "mirror". "Large mirrors" reflect "small mirrors".
  Therefore, when we "expand" from some "center", we can "reuse" some information from its "mirrored center".
  For example, we move the "center", from left to right, in the string `aiaOaia...`
  Here, the char `O` is the "large mirror".
  When the current center is the second `i`, it is "mirrored" to the first `i` (which we've calculated for),
  so we know the palindrome centered at the second `i` must have at least a length of 3 (`aia`).
  So we can expand directly from `aia`, instead of expanding from scratch.

  Manacher's algorithm is verified below.
  Also, I will verify that "every loop is entered for only `O(|s|)` times",
  which "indirectly" proves that the entire algorithm runs in `O(|s|)` time.
*/


// A reference implementation of Manacher's algorithm:
// (Ref. https://en.wikipedia.org/wiki/Longest_palindromic_substring#Manacher's_algorithm) for details...
method {:vcs_split_on_every_assert} longestPalindrome'(s: string) returns (ans: string, lo: int, hi: int)
  ensures 0 <= lo <= hi <= |s| && ans == s[lo..hi]
  ensures palindromic(s, lo, hi)
  ensures forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) :: j - i <= hi - lo
{
  var bogus: char :| true;  // an arbitrary character
  var s' := insert_bogus_chars(s, bogus);
  var radii := new int[|s'|];
  var center, radius := 0, 0;
  // vars below are just for verifying time complexity:
  ghost var loop_counter_outer, loop_counter_inner1, loop_counter_inner2 := 0, 0, 0;

  while center < |s'|
    invariant 0 <= center <= |s'|
    invariant forall i | 0 <= i < center :: max_radius(s', i, radii[i])
    invariant 0 <= radius <= |s'|
    invariant forall i | 0 <= i < center :: radii[i] >= 0
    invariant forall i | 0 <= i < center :: inbound_radius(s', i, radii[i])
    decreases |s'| - center
  {
    loop_counter_outer := loop_counter_outer + 1;

    // Stage 1: Still the normal "expand from center" routine, except `radius` is NOT necessarily zero:
    while center - (radius + 1) >= 0 && center + (radius + 1) < |s'|
        && s'[center - (radius + 1)] == s'[center + (radius + 1)]
      invariant 0 <= center < |s'|
      invariant 0 <= radius < |s'|
      invariant inbound_radius(s', center, radius)
      invariant palindromic_radius(s', center, radius)
      decreases |s'| - (center + radius)
    {
      loop_counter_inner1 := loop_counter_inner1 + 1;
      radius := radius + 1;
    }
    lemma_end_of_expansion(s', center, radius);

    radii[center] := radius;
    var old_center, old_radius := center, radius;
    center := center + 1;
    radius := 0;

    // Stage 2: Quickly infer the maximal radius, using the symmetry of known palindromes. 
    while center <= old_center + old_radius
      invariant old_center < |s'|
      invariant 0 <= center <= old_center + old_radius + 1
      invariant forall i | 0 <= i < center :: max_radius(s', i, radii[i])
      invariant 0 <= old_radius < |s'|
      decreases old_center + old_radius + 1 - center
    {
      loop_counter_inner2 := loop_counter_inner2 + 1;

      var mirrored_center := old_center - (center - old_center);
      var max_mirrored_radius := old_center + old_radius - center;
      lemma_mirrored_palindrome(s', old_center, old_radius, mirrored_center, radii[mirrored_center], center);

      if radii[mirrored_center] < max_mirrored_radius {
        radii[center] := radii[mirrored_center];
        center := center + 1;
      } else if radii[mirrored_center] > max_mirrored_radius {
        radii[center] := max_mirrored_radius;
        center := center + 1;
      } else {
        radius := max_mirrored_radius;
        break;
      }
    }
  }
  // wrap up results:
  var (c, r) := argmax(radii, 0);
  lo, hi := (c - r) / 2, (c + r) / 2; // notice that both ends are bogus chars at position 0, 2, 4, 6, etc.!
  lemma_result_transfer(s, s', bogus, radii, c, r, hi, lo);
  return s[lo..hi], lo, hi;        
}


// Below are helper functions and lemmas we used:

// Inserts bogus characters to the original string (e.g. from `abc` to `|a|b|c|`).
// Note that this is neither efficient nor necessary in reality, but just for the ease of understanding.
function {:opaque} insert_bogus_chars(s: string, bogus: char): (s': string)
  ensures |s'| == 2 * |s| + 1
  ensures forall i | 0 <= i <= |s| :: s'[i * 2] == bogus
  ensures forall i | 0 <= i < |s| :: s'[i * 2 + 1] == s[i]
{
  if s == "" then
    [bogus]
  else
    var s'_old := insert_bogus_chars(s[1..], bogus);
    var s'_new := [bogus] + [s[0]] + s'_old;
    s'_new
}

// Returns (max_index, max_value) of array `a` starting from index `start`.
function {:opaque} argmax(a: array<int>, start: int): (res: (int, int))
  reads a
  requires 0 <= start < a.Length
  ensures start <= res.0 < a.Length && a[res.0] == res.1
  ensures forall i | start <= i < a.Length :: a[i] <= res.1
{
  if start == a.Length - 1 then
    (start, a[start])
  else
    var (i, v) := argmax(a, start + 1);
    if a[start] >= v then (start, a[start]) else (i, v)
}

// Whether an interval at center `c` with a radius `r` is within the boundary of `s'`.
ghost predicate inbound_radius(s': string, c: int, r: int)
{
  r >= 0 && 0 <= c-r && c+r < |s'|
}

// Whether `r` is a valid palindromic radius at center `c`.
ghost predicate palindromic_radius(s': string, c: int, r: int)
  requires inbound_radius(s', c, r)
{
  palindromic(s', c-r, c+r+1)
}

// Whether `r` is the maximal palindromic radius at center `c`.
ghost predicate max_radius(s': string, c: int, r: int)
{
  inbound_radius(s', c, r)
  && palindromic_radius(s', c, r)
  && (forall r' | r' > r && inbound_radius(s', c, r') :: !palindromic_radius(s', c, r'))
}

// Basically, just "rephrasing" the `lemma_palindromic_contains`,
// talking about center and radius, instead of interval
lemma lemma_palindromic_radius_contains(s': string, c: int, r: int, r': int)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires 0 <= r' <= r
  ensures inbound_radius(s', c, r') && palindromic_radius(s', c, r')
{
  lemma_palindromic_contains(s', c-r, c+r+1, c-r', c+r'+1);
}

// When "expand from center" ends, we've find the max radius:
lemma lemma_end_of_expansion(s': string, c: int, r: int)
  requires inbound_radius(s', c, r) && palindromic_radius(s', c, r)
  requires inbound_radius(s', c, r + 1) ==> s'[c - (r + 1)] != s'[c + (r + 1)]
  ensures max_radius(s', c, r)
{
  forall r' | r' > r && inbound_radius(s', c, r') ensures !palindromic_radius(s', c, r') {
    if palindromic_radius(s', c, r') {  // proof by contradiction
      lemma_palindromic_radius_contains(s', c, r', r+1);
    }
  }
}

// The critical insight behind Manacher's algorithm.
//
// Given the longest palindrome centered at `c` has length `r`, consider the interval from `c-r` to `c+r`.
// Consider a pair of centers in the interval: `c1` (left half) and `c2` (right half), equally away from `c`.
// Then, the length of longest palindromes at `c1` and `c2` are related as follows:
lemma lemma_mirrored_palindrome(s': string, c: int, r: int, c1: int, r1: int, c2: int)
  requires max_radius(s', c, r) && max_radius(s', c1, r1)
  requires c - r <= c1 < c < c2 <= c + r
  requires c2 - c == c - c1
  ensures c2 + r1 < c + r ==> max_radius(s', c2, r1)
  ensures c2 + r1 > c + r ==> max_radius(s', c2, c + r - c2)
  ensures c2 + r1 == c + r ==> palindromic_radius(s', c2, c + r - c2)
{
  if c2 + r1 < c + r {
    for r2 := 0 to r1
      invariant 0 <= r2 <= r1
      invariant inbound_radius(s', c2, r2)
      invariant palindromic_radius(s', c2, r2)
    {
      // nothing to do, just for invariants
    }
    lemma_end_of_expansion(s', c2, r1);
  } else {
    for r2 := 0 to c + r - c2
      invariant 0 <= r2 <= c + r - c2
      invariant inbound_radius(s', c2, r2)
      invariant palindromic_radius(s', c2, r2)
    {
      // nothing to do, just for invariants
    }
    if c2 + r1 > c + r {
      lemma_end_of_expansion(s', c2, c + r - c2);
    }
  }
}

ghost function abs(x: int): int {
  if x >= 0 then x else -x
}

// The following returns whether `s[lo..hi]` is the longest palindrome s.t. `lo + hi == k`:
ghost predicate max_interval_for_same_center(s: string, k: int, lo: int, hi: int) {
  0 <= lo <= hi <= |s| &&
  lo + hi == k &&
  palindromic(s, lo, hi) &&
  (forall i, j | 0 <= i <= j <= |s| && palindromic(s, i, j) && i + j == k :: j - i <= hi - lo)
}

// Establishes the "palindromic isomorphism" between `s` and `s'`.
lemma lemma_palindrome_isomorph(s: string, s': string, bogus: char, lo: int, hi: int)
  requires s' == insert_bogus_chars(s, bogus)
  requires 0 <= lo <= hi <= |s| 
  ensures palindromic(s, lo, hi) <==> palindromic_radius(s', lo + hi, hi - lo)
{
  if palindromic(s, lo, hi) {  // ==>
    for r := 0 to hi - lo
      invariant 0 <= r <= hi - lo
      invariant palindromic(s, lo, hi)
    {
      // nothing to do, just for invariants
    }
  }
  i
function abs(a: real) : real {if a>0.0 then a else -a}
