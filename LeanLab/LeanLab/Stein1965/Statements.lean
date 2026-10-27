/-
P0073 M. L. Stein and P. R. Stein, "Experimental results on additive 2-bases", Math. Comp. 19
(1965) 427-434, read 2026-10-18 from papers/P0073.pdf, pages 427 to 431 of the journal (text layer
by pdftotext; every number below is a printed integer list and was compared with the text).
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN. This paper is a computation, not a proof.

Reading of the S-algorithm of Section 2, with `a_i` the primes `≥ p₀` (for `p₀ = 1` the paper also
admits 1, not used here): `b₀ = p₀`, `b₁` the next prime. Given `B = [b₀, …, b_k]`, let `2n` be the
least even number above `2 b₀` that is not a sum `b_i + b_j` and for which some `a = 2n - b_m` is an
admissible prime; `b_{k+1}` is the largest such `a` (2.3). If no prime works, `2n` is skipped, the
paper's "fails" rule. The first 22 terms printed in Section 3 for `p₀ = 3` and `p₀ = 11`, and the
statement that the first 16 terms for `p₀ = 3` cover `6 ≤ 2n ≤ 122` and `124 = 101 + 23` needs 101,
are reproduced exactly by this reading.
-/
import LeanLab.Common.Goldbach

namespace LeanLab.Stein1965

/-- `e` is a sum `b + c` of two elements of `B`, (2.2). -/
def covered (B : List Nat) (e : Nat) : Bool := B.any fun b => B.any fun c => b + c == e

/-- The largest prime `a ≥ p₀` with `a + b = e` for some `b ∈ B`, as in (2.3). -/
def bestA (p0 : Nat) (B : List Nat) (e : Nat) : Option Nat :=
  (B.filterMap fun b => if b < e && p0 ≤ e - b && primeB (e - b) then some (e - b) else none).foldl
    (fun acc a => match acc with | none => some a | some x => some (max x a)) none

/-- Search upward from `e` for the least uncovered even that some prime reaches. -/
def findNew (p0 : Nat) (B : List Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, e =>
    if covered B e then findNew p0 B fuel (e + 2) else
      match bestA p0 B e with
      | some a => some a
      | none => findNew p0 B fuel (e + 2)

/-- The least prime `≥ n`, with fuel. -/
def nextPrime (n : Nat) : Nat → Nat
  | 0 => n
  | f + 1 => if primeB n then n else nextPrime (n + 1) f

/-- The first `len` terms of the S-sequence `{b_i}_{p₀}`. -/
def steinSeq (p0 len : Nat) : List Nat :=
  (List.range (len - 2)).foldl
    (fun B _ => match findNew p0 B 100000 (2 * B.head! + 2) with
      | some a => B ++ [a]
      | none => B)
    [p0, nextPrime (p0 + 1) 10]

/-- Section 3, page 428: the first 22 terms of `{b_i}_3`. -/
def printedSeq3 : List Nat :=
  [3, 5, 7, 13, 19, 23, 31, 37, 43, 47, 53, 61, 79, 83, 109, 113, 101, 131, 139, 157, 167, 199]

/-- Section 3, page 428: the first 22 terms of `{b_i}_11`. -/
def printedSeq11 : List Nat :=
  [11, 13, 17, 19, 29, 31, 41, 43, 53, 37, 59, 79, 73, 113, 109, 103, 107, 151, 163, 167, 179, 191]

end LeanLab.Stein1965
