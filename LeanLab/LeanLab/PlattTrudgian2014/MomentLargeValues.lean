/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 pages 29 to 30, displays 42 and 43.
The general conclusions remain CONDITIONAL ON the explicit moment or block certificate.
-/
import LeanLab.PlattTrudgian2014.BlockPressure

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex Finset

/-- CONDITIONAL ON MomentEnvelope. -/
theorem projectedSet_of_envelope {t A b : ℝ} (ht : 0 < t) (he : MomentEnvelope t A b)
    (L : ℕ) (a : ℝ) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) :
    (volume (projectedSet L a ρ)).toReal ≤ A * Real.exp ((b - t * a) * L) := by
  have hm := (projectedSet_markov L a ht ρ).trans (he L ρ hρ)
  have hh : (volume (projectedSet L a ρ)).toReal ≤
      A * Real.exp (b * L) / Real.exp (t * (a * L)) := by
    rw [le_div_iff₀ (Real.exp_pos _)]
    nlinarith
  calc
    _ ≤ A * Real.exp (b * L) / Real.exp (t * (a * L)) := hh
    _ = A * Real.exp ((b - t * a) * L) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- CONDITIONAL ON MomentEnvelope. -/
theorem bigSet_of_envelope {t A b a lam : ℝ} (ht : 0 < t) (hA : 0 ≤ A)
    (he : MomentEnvelope t A b) (ha : 0 < a) (hal : a < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      (volume (bigSet N lam)).toReal ≤ C * Real.exp (-(t * a - b) * Lof N) := by
  classical
  have hl : 0 < lam := ha.trans hal
  have hε : 0 < 1 - a / lam := by rw [sub_pos, div_lt_one hl]; exact hal
  obtain ⟨D, hD, hnet⟩ := exists_finite_directions hε
  refine ⟨D.card * A, mul_nonneg (Nat.cast_nonneg _) hA, fun N _ => ?_⟩
  let U := ⋃ ρ ∈ D, projectedSet (Lof N) a ρ
  have hcover : bigSet N lam ⊆ U := by
    intro x hx
    have hn : G (Lof N) x ≠ 0 := by
      apply norm_ne_zero_iff.mp
      exact ne_of_gt ((mul_nonneg hl.le (Nat.cast_nonneg _)).trans_lt hx.2)
    obtain ⟨ρ, hρ, hp⟩ := hnet (G (Lof N) x) hn
    apply Set.mem_iUnion₂.mpr
    refine ⟨ρ, hρ, hx.1, ?_⟩
    have haL : a * Lof N ≤ (1 - (1 - a / lam)) * ‖G (Lof N) x‖ := by
      have hf : a * Lof N = (a / lam) * (lam * Lof N) := by field_simp
      rw [show 1 - (1 - a / lam) = a / lam by ring, hf]
      exact mul_le_mul_of_nonneg_left hx.2.le (div_nonneg ha.le hl.le)
    exact haL.trans hp
  have hU : volume U ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Set.Icc (0 : ℝ) 1) ≠ ⊤ by simp)
    apply measure_mono
    intro x hx
    obtain ⟨ρ, _, hp⟩ := Set.mem_iUnion₂.mp hx
    exact hp.1
  calc
    _ ≤ volume.real U := measureReal_mono hcover hU
    _ ≤ ∑ ρ ∈ D, (volume (projectedSet (Lof N) a ρ)).toReal :=
      measureReal_biUnion_finset_le D _
    _ ≤ ∑ ρ ∈ D, A * Real.exp ((b - t * a) * Lof N) :=
      sum_le_sum fun ρ hρ => projectedSet_of_envelope ht he _ _ (hD ρ hρ).le
    _ = (D.card : ℝ) * A * Real.exp (-(t * a - b) * Lof N) := by
      simp only [sum_const, nsmul_eq_mul]
      rw [show (b - t * a) * (Lof N : ℝ) = -(t * a - b) * Lof N by ring]
      ring

/-- CONDITIONAL ON MomentEnvelope. -/
theorem lambdaOK_of_envelope {c lam a t A b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hal : a < lam)
    (ht : 0 < t) (hA : 0 ≤ A) (he : MomentEnvelope t A b)
    (hgap : c * Real.log 2 < t * a - b) : LambdaOK c lam := by
  obtain ⟨C, hC, hvol⟩ := bigSet_of_envelope ht hA he ha hal
  apply lambdaOK_of_exp_decay hC _ hgap hvol
  exact (mul_nonneg hc (Real.log_pos (by norm_num)).le).trans hgap.le

/-- CONDITIONAL ON BlockBound. -/
theorem lambdaOK_of_block {c lam a t F : ℝ} {h : ℕ} (hh : 0 < h) (hc : 0 ≤ c)
    (ha : 0 < a) (hal : a < lam) (ht : 0 < t) (hb : BlockBound h t F)
    (hgap : c * Real.log 2 < t * a - Real.log F / h) : LambdaOK c lam :=
  lambdaOK_of_envelope hc ha hal ht (Real.exp_nonneg _) (block_moment_envelope hh ht.le hb) hgap

#print axioms projectedSet_of_envelope
#print axioms bigSet_of_envelope
#print axioms lambdaOK_of_envelope
#print axioms lambdaOK_of_block

end LeanLab.PlattTrudgian2014
