/-
Platt-Trudgian 2014, P0024, F-5009 recheck after the author's reply of 2026-10-19:
D. Platt says the j loop of Algorithm 1 should run 2 to ε(d), and that his C code does so.
Here: the printed in-place update with only the loop bound changed to ε(d) is still wrong,
465 at d = 11, K = 2, true minimum 9; the per-k step that sums shifts of the vector held at
the start of that k step, j = 2 to ε(d), reproduces H exactly at the checked cases.
So the author's point is one of the two corrections F-5009 named; the other, a separate
buffer for the shifted copy, is presumably what his C loop does.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PlattTrudgian2014.Section2

namespace LeanLab.PlattTrudgian2014.Section2

open Finset

/-- The printed in-place update with the j loop run 2 to ε(d), the author's bound. -/
def alg1WAuthorBound (d e K : ℕ) : ZMod d → ℕ :=
  let W0 : ZMod d → ℕ := fun i =>
    ((Finset.Icc 1 e).filter fun ν => ((2 * (K - 1) + 2 ^ ν : ℕ) : ZMod d) = i).card
  let inner (W : ZMod d → ℕ) : ZMod d → ℕ :=
    ((List.range' 2 (e - 1)).foldl fun W j => alg1Step d W ((2 ^ j - 2 : ℕ) : ZMod d)) W
  (List.range (K - 1)).foldl (fun W _ => inner W) W0

/-- The buffered step: W_new(i) = W(i) + Σ_{j=2}^{ε} W(i − (2^j − 2)), W held fixed. -/
def alg1WBuffered (d e K : ℕ) : ZMod d → ℕ :=
  let W0 : ZMod d → ℕ := fun i =>
    ((Finset.Icc 1 e).filter fun ν => ((2 * (K - 1) + 2 ^ ν : ℕ) : ZMod d) = i).card
  let step (W : ZMod d → ℕ) : ZMod d → ℕ := fun i =>
    W i + ((List.range' 2 (e - 1)).map fun j => W (i - ((2 ^ j - 2 : ℕ) : ZMod d))).sum
  (List.range (K - 1)).foldl (fun W _ => step W) W0

theorem authorBound_3_2 : univ.inf' univ_nonempty (alg1WAuthorBound 3 2 2) = 1 := by decide

theorem authorBound_11_2 : univ.inf' univ_nonempty (alg1WAuthorBound 11 10 2) = 465 := by
  decide

/-- The author's loop bound alone does not fix the in-place update at d = 11, K = 2. -/
theorem authorBound_wrong_11_2 :
    univ.inf' univ_nonempty (alg1WAuthorBound 11 10 2) ≠ univ.inf' univ_nonempty (H 11 10 2) := by
  rw [authorBound_11_2, H_11_2_min]; decide

theorem buffered_3_2 : alg1WBuffered 3 2 2 = H 3 2 2 := by decide

theorem buffered_11_2 : alg1WBuffered 11 10 2 = H 11 10 2 := by decide

theorem buffered_7_3 : alg1WBuffered 7 3 3 = H 7 3 3 := by decide

end LeanLab.PlattTrudgian2014.Section2
