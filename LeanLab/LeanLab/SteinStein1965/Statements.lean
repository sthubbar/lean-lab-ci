/-
Stein and Stein 1965, "Experimental results on additive 2-bases", Math. Comp. 19, 427-434.
Paper P0073, unit U-0954, run 20261018T1603Z-12862.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.

This file defines the S-algorithm of Section 2, pp. 427-428, as a Lean function and states
the paper's claims. Goldbach's conjecture is OPEN; nothing here proves it. The paper's
verification up to `10^7` is far below published records and is only stated, cited.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.SteinStein1965

/-! ### Binary additive bases -/

/-- `B` is a binary additive basis for the even numbers `m` with `lo ≤ m ≤ hi`, eq. (2.1):
every such `m` is `b_i + b_j` with `b_i, b_j ∈ B`. -/
def IsBasisFor (B : List ℕ) (lo hi : ℕ) : Prop :=
  ∀ m, m % 2 = 0 → lo ≤ m → m ≤ hi → ∃ x ∈ B, ∃ y ∈ B, x + y = m

/-! ### The S-algorithm, Section 2, eqs. (2.2), (2.3), p. 427, and the failure rule p. 428

The input set `{a_i}` is given by a Boolean predicate `isA` together with its two smallest
elements `a0 < a1`. The paper takes `b0 = a0`, `b1 = a1`, then scans the even numbers
`2n* > 2 b0` upward. At each even `m` not yet a sum `S_ij = b_i + b_j` it adds
`b_{k+1} = max { a ∈ {a_i} : a + b_m = m for some basis element b_m }`, eq. (2.3).
If no such `a` exists the algorithm "fails" at `m`; it records `m` and moves on to `m + 2`,
p. 428. The output is the list of basis elements in generation order, which is not sorted:
the paper's "backtracking", and the list of failed evens. -/

/-- `m` is already a sum of two elements of `bs`. -/
def covers (bs : List ℕ) (m : ℕ) : Bool :=
  bs.any fun x => decide (x ≤ m) && bs.contains (m - x)

/-- Candidates `a = m - b` with `b` in the current basis and `a ∈ {a_i}`. -/
def cands (isA : ℕ → Bool) (bs : List ℕ) (m : ℕ) : List ℕ :=
  (bs.filter fun b => decide (b ≤ m) && isA (m - b)).map (m - ·)

/-- One step of the S-algorithm at the even number `m`. State: basis, failures. -/
def step (isA : ℕ → Bool) (st : List ℕ × List ℕ) (m : ℕ) : List ℕ × List ℕ :=
  if covers st.1 m then st
  else match (cands isA st.1 m).max? with
    | some a => (st.1 ++ [a], st.2)
    | none => (st.1, st.2 ++ [m])

/-- The even numbers `m` with `lo ≤ m ≤ hi`, increasing. -/
def evensIn (lo hi : ℕ) : List ℕ :=
  (List.range' lo (hi + 1 - lo)).filter fun m => m % 2 == 0

/-- The S-algorithm run on all evens `2 a0 ≤ 2n* ≤ N1`. Returns `(basis, failures)`. -/
def sAlg (isA : ℕ → Bool) (a0 a1 N1 : ℕ) : List ℕ × List ℕ :=
  (evensIn (2 * a0) N1).foldl (step isA) ([a0, a1], [])

/-! ### The prime case, Section 3 -/

/-- The input set for the prime case starting at `p0`: odd primes `≥ p0`, and also `1`
when `p0 = 1`, since the paper counts 1 as a prime, Table I column `B(1; x)` and p. 434. -/
def primeA (p0 : ℕ) (n : ℕ) : Bool :=
  decide (p0 ≤ n) && (n == 1 || (n != 2 && primeB n))

/-- The second element `a1` of the prime input set: the next odd prime after `p0`. By
Bertrand's postulate it lies below `2 p0 + 4`. -/
def nextA (p0 : ℕ) : ℕ :=
  ((List.range' (p0 + 1) (p0 + 3)).find? fun n => n != 2 && primeB n).getD 0

/-- `{b_i}_{p0}`, the prime S-sequence of Section 3 computed for `2n* ≤ N1`. -/
def sPrime (p0 N1 : ℕ) : List ℕ × List ℕ := sAlg (primeA p0) p0 (nextA p0) N1

/-- `B(p0; x)`, p. 429: number of elements `≤ x` of `{b_i}_{p0}`, read off a run to `N1`. -/
def Bcount (p0 x N1 : ℕ) : ℕ := ((sPrime p0 N1).1.filter (· ≤ x)).length

/-- `C(u, v; x)`, p. 429: number of primes common to `{b_i}_u` and `{b_i}_v` up to `x`. -/
def Ccount (u v x : ℕ) : ℕ :=
  (((sPrime u x).1.filter (· ≤ x)).filter fun b => (sPrime v x).1.contains b).length

/-- Table V, p. 433: number of the evens `2n*` of eq. (2.3) that are multiples of 6,
that is targets that produced a new element, for `2n* ≤ x`. The two seed elements
`b0, b1` have no target in this count. -/
def tableVCount (p0 x : ℕ) : ℕ :=
  ((evensIn (2 * p0) x).filter fun m =>
    m % 6 == 0 && !(covers (sPrime p0 (m - 2)).1 m) &&
      ((cands (primeA p0) (sPrime p0 (m - 2)).1 m).max?).isSome).length

/-! ### Claims of the paper -/

/-- Section 3, p. 429, and Section 2, p. 428: with `p0 = 3` the S-algorithm never fails for
`6 ≤ 2n ≤ 10^7`, so `{b_i}_3` is a basis for those evens. Cited, not re-run: the range is far
below published Goldbach verifications and is retired under the lab's finite check gate. -/
def SBasisClaim3 : Prop := (sPrime 3 (10 ^ 7)).2 = []

/-- Section 3, p. 429: the same for `p0 = 1`, `N0 = 2`. -/
def SBasisClaim1 : Prop := (sPrime 1 (10 ^ 7)).2 = []

/-- Abstract and Section 3, p. 429: Goldbach for every even `4 ≤ 2n ≤ 10^7`. -/
def GoldbachClaim : Prop := EvenGoldbachUpTo (10 ^ 7)

/-- Section 3, p. 429: `B(1; 10^7) = 10474`, `B(3; 10^7) = 10576`, `C(1, 3; 10^7) = 288`. -/
def Claim1e7 : Prop :=
  Bcount 1 (10 ^ 7) (10 ^ 7) = 10474 ∧ Bcount 3 (10 ^ 7) (10 ^ 7) = 10576 ∧
    Ccount 1 3 (10 ^ 7) = 288

/-- Section 5, p. 433: `B(7; 7 * 10^6) = 13108`. -/
def Claim7 : Prop := Bcount 7 (7 * 10 ^ 6) (7 * 10 ^ 6) = 13108

/-- Table I, p. 430, header: the lower limits `N0` for the twelve `p0`. For each pair
`(p0, N0)`, with `x = 5 * 10^6`, `{b_i}_{p0}` is a basis for `N0 ≤ 2n ≤ x` and `N0 - 2` is not
a sum of two of its elements. -/
def tableI_N0 : List (ℕ × ℕ) :=
  [(1, 2), (3, 6), (5, 10), (7, 18), (11, 22), (13, 30),
   (71, 166), (73, 166), (79, 176), (83, 190), (89, 190), (97, 198)]

def TableI_N0Claim (x : ℕ) : Prop :=
  ∀ r ∈ tableI_N0, IsBasisFor (sPrime r.1 x).1 r.2 x ∧
    ¬ ∃ u ∈ (sPrime r.1 x).1, ∃ v ∈ (sPrime r.1 x).1, u + v = r.2 - 2

/-- Table I, p. 430, body: `B(p0; 2 * 10^5 * k)` for `k = 1, ..., 25`, read off the run
to `5 * 10^6`. Entries transcribed from the rendered page image. -/
def tableI : List (ℕ × List ℕ) :=
  [(1, [1235,1820,2265,2658,3000,3307,3598,3868,4123,4377,4612,4826,5057,5268,5472,5656,5857,
        6045,6218,6405,6568,6733,6896,7057,7211]),
   (3, [1245,1837,2288,2681,3029,3337,3623,3909,4178,4421,4661,4883,5108,5318,5517,5710,5880,
        6078,6271,6452,6609,6787,6948,7110,7274]),
   (5, [1263,1844,2300,2688,3027,3360,3640,3919,4178,4416,4656,4882,5087,5298,5505,5699,5891,
        6071,6260,6426,6598,6749,6920,7086,7256]),
   (7, [1287,1970,2566,3089,3588,4074,4508,4955,5344,5747,6133,6514,6875,7216,7568,7892,8210,
        8523,8820,9132,9450,9741,10020,10299,10579]),
   (11, [1236,1822,2268,2663,3005,3300,3599,3881,4130,4382,4615,4837,5048,5251,5454,5647,5832,
        6021,6204,6383,6548,6719,6889,7045,7220]),
   (13, [1233,1813,2264,2654,3008,3315,3613,3882,4131,4390,4610,4832,5050,5250,5458,5643,5828,
        6023,6205,6387,6550,6707,6877,7029,7186]),
   (71, [1231,1803,2259,2644,2984,3294,3580,3864,4125,4359,4603,4831,5042,5254,5455,5636,5835,
        6021,6201,6376,6539,6720,6876,7031,7181]),
   (73, [1239,1814,2266,2652,2996,3308,3593,3861,4120,4368,4609,4824,5045,5252,5460,5642,5831,
        6017,6190,6378,6537,6707,6866,7021,7177]),
   (79, [1247,1809,2267,2657,2991,3317,3609,3885,4139,4371,4603,4832,5046,5255,5449,5638,5817,
        6012,6192,6374,6544,6704,6872,7033,7185]),
   (83, [1239,1821,2277,2661,3002,3319,3595,3884,4127,4374,4610,4835,5046,5247,5459,5658,5840,
        6015,6215,6377,6553,6721,6876,7028,7182]),
   (89, [1246,1811,2263,2644,2994,3308,3606,3875,4128,4368,4614,4829,5035,5246,5448,5640,5833,
        6020,6188,6369,6534,6703,6869,7027,7186]),
   (97, [1239,1815,2270,2660,2989,3302,3594,3867,4117,4366,4589,4813,5024,5236,5437,5627,5814,
        6008,6180,6358,6528,6696,6860,7028,7178])]

/-- Table I as a claim about the Lean S-algorithm. Our Python recomputation disagrees with
some entries, see STATEMENTS.md; so this is stated, not asserted. -/
def TableIClaim : Prop :=
  ∀ r ∈ tableI, ∀ k < 25, Bcount r.1 (200000 * (k + 1)) (5 * 10 ^ 6) = r.2.getD k 0

/-- Table II-a and II-b, p. 431: `C(u, v; 5 * 10^6)`. -/
def tableII : List (ℕ × ℕ × ℕ) :=
  [(1,3,250),(1,5,253),(1,11,282),(1,13,269),(3,5,251),(3,11,263),(3,13,258),(5,11,237),
   (5,13,275),(11,13,274),
   (71,73,264),(71,79,253),(71,83,280),(71,89,259),(71,97,290),(73,79,284),(73,83,244),
   (73,89,269),(73,97,286),(79,83,272),(79,89,269),(79,97,239),(83,89,301),(83,97,300),
   (89,97,281)]

def TableIIClaim : Prop := ∀ r ∈ tableII, Ccount r.1 r.2.1 (5 * 10 ^ 6) = r.2.2

/-- Table V, p. 433. -/
def tableV : List (ℕ × ℕ) :=
  [(1,33),(3,45),(5,30),(7,18),(11,33),(13,42),(71,38),(73,27),(79,30),(83,30),(89,31),(97,41)]

def TableVClaim : Prop := ∀ r ∈ tableV, tableVCount r.1 (5 * 10 ^ 6) = r.2

/-- Table IV, p. 432, primes column: the number of gaps of size `g` between consecutive
primes `≤ 10^6`, for `g = 2, 4, ..., 56`. The random-set columns cannot be stated: the sets
RO(j) are not given in the paper. -/
def tableIVPrimes : List ℕ :=
  [8169,8143,13549,5569,7079,8005,4233,2881,4909,2401,2172,2682,1175,1234,1914,550,557,767,
   330,424,476,202,155,196,106,77,140,53]

/-- Number of `p ≤ X` prime with `p + g` the next prime and `p + g ≤ X`. -/
def gapCount (X g : ℕ) : ℕ :=
  ((List.range (X + 1)).filter fun p =>
    primeB p && decide (p + g ≤ X) && primeB (p + g) &&
      (List.range' (p + 1) (g - 1)).all fun q => !primeB q).length

def TableIVClaim : Prop :=
  ∀ k < 28, gapCount (10 ^ 6) (2 * (k + 1)) = tableIVPrimes.getD k 0

/-! ### Note added in proof, pp. 433-434 -/

/-- `q` is the least odd prime `≥ 3` with `N - q` prime: the paper's `P(2n)`. -/
def IsLeastGoldbachPrime (N q : ℕ) : Prop :=
  3 ≤ q ∧ q.Prime ∧ (N - q).Prime ∧ ∀ r, 3 ≤ r → r < q → r.Prime → ¬ (N - r).Prime

/-- Numbers that are `1` or a prime `≡ 1 mod 4`, p. 434, "here 1 is counted as a prime". -/
def IsP1 (n : ℕ) : Prop := n = 1 ∨ (n.Prime ∧ n % 4 = 1)

/-- The least `q` with `q` and `N - q` both in `IsP1`: the paper's `P(2n)` for `4m + 2`. -/
def IsLeastP1Pair (N q : ℕ) : Prop :=
  q ≤ N ∧ IsP1 q ∧ IsP1 (N - q) ∧ ∀ r, r < q → IsP1 r → ¬ IsP1 (N - r)

/-- p. 433: for `63276 ≤ 2n ≤ 10^8`, `P(2n) < √(2n)`. Cited, a Goldbach range claim. -/
def NoteClaimP : Prop :=
  ∀ N, N % 2 = 0 → 63276 ≤ N → N ≤ 10 ^ 8 → ∃ q, IsLeastGoldbachPrime N q ∧ q * q < N

/-- p. 434: for `1457284 ≤ 2n = 4m + 2 < 10^8`, `P(2n) < √(2n)` in the `4k + 1` version. -/
def NoteClaimP1 : Prop :=
  ∀ N, N % 4 = 2 → 1457284 ≤ N → N < 10 ^ 8 → ∃ q, IsLeastP1Pair N q ∧ q * q < N

/-- The cited verification itself. -/
theorem goldbach_1e7_cited : GoldbachClaim := by
  sorry

/-- The cited S-basis runs, Section 3, p. 429. -/
theorem sBasis3_cited : SBasisClaim3 := by
  sorry

theorem sBasis1_cited : SBasisClaim1 := by
  sorry

theorem noteP_cited : NoteClaimP := by
  sorry

theorem noteP1_cited : NoteClaimP1 := by
  sorry

/-- Section 5, p. 433: `B(7; 7 * 10^6) = 13108`. Cited; our Python recomputation agrees. -/
theorem claim7_cited : Claim7 := by
  sorry

/-- Table IV primes column, p. 432. Cited; our Python recomputation agrees in all 28 rows. -/
theorem tableIV_cited : TableIVClaim := by
  sorry

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.goldbach_1e7_cited
#print axioms LeanLab.SteinStein1965.sBasis3_cited
#print axioms LeanLab.SteinStein1965.sBasis1_cited
#print axioms LeanLab.SteinStein1965.noteP_cited
#print axioms LeanLab.SteinStein1965.noteP1_cited
#print axioms LeanLab.SteinStein1965.claim7_cited
#print axioms LeanLab.SteinStein1965.tableIV_cited
