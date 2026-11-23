/-
Twin proof of the LEAF `leaf8_summable` of `Split1122bSeries8.lean`.

Source: Bordignon, Johnston, Starichkova, arXiv 2207.09452, page 6, display 18 with
Lemma 8: 0 ≤ f_n(s) ≤ 2 e^2 c_n^(n-1) h(s), with c_n = 0.9607 for n > 500, so the
series 13 and 14 are dominated by a geometric series beyond n = 500.

This file proves `leaf8_summable_twin`, a twin of the LEAF `leaf8_summable`,
CONDITIONAL ON leaf306_display18 and the LEAFs it rests on in `Split306Theorem6.lean`.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bSeries8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- The geometric majorant beyond n = 500: 2 e^2 · 0.9607^(n+500) · |h(s)|. -/
def majS8 (s : ℝ) (n : ℕ) : ℝ :=
  (2 * exp 2 * (0.9607 : ℝ) ^ 500 * |LeanLab.ChenExplicit.hSieve s|) * (0.9607 : ℝ) ^ n

/-- The majorant is summable, being a constant times a geometric series of ratio 0.9607. -/
theorem majS8_summable (s : ℝ) : Summable (majS8 s) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- The majorant is nonnegative. -/
theorem majS8_nonneg (s : ℝ) (n : ℕ) : 0 ≤ majS8 s n := by
  unfold majS8; positivity

/-- Display 18 beyond 500, rewritten against the majorant: for n = m + 501 with the
parity and range hypotheses of BJS, f_n(s) ≤ majS8 s m. -/
theorem fn_le_majS8 (m : ℕ) (s : ℝ)
    (hs : (Odd (m + 501) ∧ 1 ≤ s) ∨ (Even (m + 501) ∧ 2 ≤ s)) :
    bjsF306 (m + 501) s ≤ majS8 s m := by
  have h := leaf306_display18 (m + 501) (by omega) s hs
  rw [bjsC306_large (m + 501) (by omega)] at h
  have he : m + 501 - 1 = 500 + m := by omega
  rw [he, pow_add] at h
  refine h.trans ?_
  unfold majS8
  have : 0 ≤ 2 * exp 2 * ((0.9607 : ℝ) ^ 500 * (0.9607 : ℝ) ^ m) := by positivity
  calc 2 * exp 2 * ((0.9607 : ℝ) ^ 500 * (0.9607 : ℝ) ^ m) * LeanLab.ChenExplicit.hSieve s
      ≤ 2 * exp 2 * ((0.9607 : ℝ) ^ 500 * (0.9607 : ℝ) ^ m) * |LeanLab.ChenExplicit.hSieve s| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) this
    _ = _ := by ring

/-- Summability of a parity restricted series from the tail bound: if the parity
condition `P` gives the hypotheses of display 18, the restricted series is summable. -/
theorem summable_parity_s8 (P : ℕ → Prop) [DecidablePred P] (s : ℝ)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    Summable (fun n : ℕ => if P n then bjsF306 n s else 0) := by
  rw [← summable_nat_add_iff 501]
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (majS8_summable s)
  · split_ifs with h
    · exact leaf306_fn_nonneg _ s (hP _ h)
    · exact le_refl 0
  · split_ifs with h
    · exact fn_le_majS8 m s (hP _ h)
    · exact majS8_nonneg s m

/-- Twin of the LEAF `leaf8_summable` of `Split1122bSeries8.lean`: the series 13 and 14
of BJS page 6 converge, by display 18 and Lemma 8.
CONDITIONAL ON leaf306_display18. -/
theorem leaf8_summable_twin :
    (∀ s : ℝ, 1 ≤ s → Summable (fun n : ℕ => if Odd n then bjsF306 n s else 0)) ∧
    (∀ s : ℝ, 2 ≤ s → Summable (fun n : ℕ => if Even n then bjsF306 n s else 0)) :=
  ⟨fun s hs => summable_parity_s8 Odd s (fun _ h => Or.inl ⟨h, hs⟩),
   fun s hs => summable_parity_s8 Even s (fun _ h => Or.inr ⟨h, hs⟩)⟩

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf8_summable_twin
