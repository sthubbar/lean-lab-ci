/-
Unit U-1614, run 20261104T0803Z-26516. Refutations of `DecompJ251.theorem3_2` and `lemma2_6`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.KadiriLumley2014.DecompJ251

namespace LeanLab.KadiriLumley2014.Audit1614
open Real Set MeasureTheory
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- First row of Table 2. -/
def r0 : PrintedRow := ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩

theorem r0_mem : r0 ∈ tableTwo := by
  unfold tableTwo; exact List.mem_cons_self

theorem weight_pos {m : ℕ} {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < weight m t := by
  unfold weight
  have : 0 < 4 * t * (1 - t) := by
    have : 0 < 1 - t := by linarith
    positivity
  positivity

theorem weight_int_pos (m : ℕ) {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1) :
    0 < ∫ t in (0 : ℝ)..a, weight m t := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply Continuous.intervalIntegrable
    unfold weight
    fun_prop
  · intro t ht
    exact weight_pos ht.1 (lt_of_lt_of_le ht.2 h1)
  · exact h0

theorem exp38 : (10 : ℝ) ^ 13 ≤ Real.exp 38 := by
  have h : Real.exp 38 = Real.exp 1 ^ 38 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h2 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  calc (10 : ℝ) ^ 13 ≤ (2.7 : ℝ) ^ 38 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 38

/-- The old `theorem3_2`: every factor is positive, at the first row, `a = aQ`, `X = exp 38`. -/
theorem old_theorem3_2_false :
    ¬ ∀ {r : PrintedRow} (_ : r ∈ tableTwo) {a X : ℝ}
      (_ : a ∈ Icc (r.aQ : ℝ) ((r.aQ : ℝ) + 1 / 10000)) (_ : Real.exp 38 ≤ X),
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a /
        (∫ t in (0 : ℝ)..1, weight r.m t) ≤ 0 := by
  intro h
  have hs := table_small_steps r0 r0_mem
  have hd : (0 : ℝ) < (r0.deltaQ : ℝ) := by exact_mod_cast hs.1
  have hu : ((1 : ℝ) / 10 ^ 12) ≤ (r0.uQ : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    norm_num at h' ⊢
    linarith
  have ha : ((r0.aQ : ℚ) : ℝ) = 2129 / 10000 := by
    norm_num [r0, PrintedRow.aQ]
  have key := h r0_mem (a := (r0.aQ : ℝ)) (X := Real.exp 38)
    ⟨le_rfl, by linarith⟩ le_rfl
  refine absurd key (not_le.mpr (div_pos (mul_pos ?_ ?_) (weight_int_pos _ one_pos le_rfl)))
  · set u : ℝ := (r0.uQ : ℝ)
    set d : ℝ := (r0.deltaQ : ℝ)
    have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
    have he : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
    have he0 : 0 < Real.exp u - 1 := by linarith
    have hX := exp38
    have hbig : 1 < Real.exp 38 * (Real.exp u - 1) := by
      have : (10 : ℝ) ^ 13 * (1 / 10 ^ 12) ≤ Real.exp 38 * (Real.exp u - 1) :=
        mul_le_mul hX (by linarith) (by norm_num) (Real.exp_pos _).le
      norm_num at this ⊢
      linarith
    have hnum : 1 < Real.exp u * Real.exp 38 * (1 + d) := by
      have h1 : 1 ≤ Real.exp u := Real.one_le_exp hu0.le
      have h2 : (1 : ℝ) < Real.exp 38 := by
        have : (1 : ℝ) < 10 ^ 13 := by norm_num
        linarith
      have h3 : 1 < Real.exp u * Real.exp 38 := by nlinarith
      nlinarith
    unfold tailCoefficient
    have l1 := Real.log_pos hbig
    have l2 := Real.log_pos hnum
    have hX0 := Real.exp_pos 38
    positivity
  · unfold tailMass
    have ha0 : (0 : ℝ) < (r0.aQ : ℝ) := by rw [ha]; norm_num
    have ha1 : ((r0.aQ : ℝ)) ≤ 1 := by rw [ha]; norm_num
    rw [weight_tail_symm]
    have := weight_int_pos r0.m ha0 ha1
    linarith

/-- `lemma2_6` says `zeroError ≤ 0`. If the family is summable, as `Decomp92.smoothed_explicit_lower`
asserts, and one zero contributes, this fails. -/
theorem old_lemma2_6_false_of_summable {m : ℕ} {δ u X : ℝ}
    (hX : 0 ≤ X) (hs : Summable (zeroSummand m δ u X))
    (ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1}) (hρ : 0 < zeroSummand m δ u X ρ) :
    ¬ zeroError m δ u X ≤ 0 := by
  unfold zeroError
  exact not_le.mpr (hs.tsum_pos (fun ρ => zeroSummand_nonneg m δ u hX ρ) ρ hρ)

end LeanLab.KadiriLumley2014.Audit1614
#print axioms LeanLab.KadiriLumley2014.Audit1614.old_theorem3_2_false
#print axioms LeanLab.KadiriLumley2014.Audit1614.old_lemma2_6_false_of_summable
