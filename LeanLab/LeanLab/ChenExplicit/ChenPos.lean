/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6402, track T2.
P0009 BJS 2022: Chen's theorem itself, a POSITIVE count of representations N = p + P₂, from the
Section 9 combination of Theorems 44, 50, 51, with any constant κ in place of the 2·10⁻⁴ of
Theorem 3. `chenCount_gt_of_sieveBounds` is AssemblyT.lean's `BJS3At_of_sieveBounds`, run
20261018T0903Z-17311, copied verbatim with 2·10⁻⁴ replaced by a parameter κ and the last rewrite dropped; `chenPos_of_sieveBounds`
takes κ > 0. The paper's headline, every even N > exp(exp 32.7) is a prime plus a number with at
most two prime factors, needs only this positive form. Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT

open Finset Real

noncomputable section
namespace LeanLab.ChenExplicit

/-- Chen's theorem above exp(exp t): every even N > exp(exp t) has a representation counted by `chenCount`. -/
def ChenPosAt (t : ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → 0 < chenCount N

/-- The Section 9 margin with constant κ in place of 2·10⁻⁴. -/
def MarginKAt (t κ : ℝ) (cA cQ cB : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → κ + 1 / 10 ^ 12 ≤ cA N - cQ N / 2 - cB N / 2

theorem chenCount_gt_of_sieveBounds (t : ℝ) (ht : 327 / 10 ≤ t) (κ : ℝ) (cA cQ cB : ℕ → ℝ)
    (hA : Thm44At t cA) (hQ : Thm50At t cQ) (hB : Thm51At t cB) (hm : MarginKAt t κ cA cQ cB) :
    ∀ N : ℕ, Even N → exp (exp t) < N → κ * mainTerm N < chenCount N := by
  intro N hEven hNt
  have hN : exp (exp (327 / 10)) < (N : ℝ) :=
    lt_of_le_of_lt (exp_le_exp.mpr (exp_le_exp.mpr ht)) hNt
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : exp (327 / 10) < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL6 := exp_32_7_gt
  have hL0 : 0 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hz2 : 2 ≤ zN N := by
    rw [hz]; have := add_one_le_exp (L / 8); linarith
  have hy0 : 0 < yN N := by rw [hy]; exact exp_pos _
  have hy3 : (N : ℝ) ≤ yN N ^ 3 := by
    rw [hy, ← exp_nat_mul, hNe]; apply exp_le_exp.mpr; push_cast; linarith
  have hchen := chen_inequality N (zN N) (yN N) hz2 hy0 hy3
  have h1 := hA N hEven hNt
  have h2 := hQ N hEven hNt
  have h3 := hB N hEven hNt
  have hmN := hm N hEven hNt
  have hU := U_ge N
  have hL2 : 0 < L ^ 2 := by positivity
  have hM0 : 0 < mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  -- the error terms of Lemma 37
  have hE : 2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * mainTerm N := by
    have hbig := big_exp L hL.le
    have e1 : 2 * (N : ℝ) / zN N = 2 * exp (7 * L / 8) := by
      rw [hz, hNe, mul_div_assoc, ← exp_sub]; ring_nf
    have e2 : yN N ≤ exp (7 * L / 8) := by rw [hy]; exact exp_le_exp.mpr (by linarith)
    have e3 : exp L = exp (7 * L / 8) * exp (L / 8) := by rw [← exp_add]; ring_nf
    have hM : 1 / 1000 * exp L / L ^ 2 ≤ mainTerm N := by
      simp only [mainTerm]; rw [← hLdef, ← hNe]
      apply div_le_div_of_nonneg_right _ hL2.le
      rw [hNe]; exact mul_le_mul_of_nonneg_right hU (exp_pos _).le
    have h7 := exp_pos (7 * L / 8)
    have : 3 * exp (7 * L / 8) ≤ 1 / 10 ^ 12 * (1 / 1000 * exp L / L ^ 2) := by
      rw [e3, show 1 / 10 ^ 12 * (1 / 1000 * (exp (7 * L / 8) * exp (L / 8)) / L ^ 2) =
        exp (7 * L / 8) * exp (L / 8) / (10 ^ 15 * L ^ 2) by ring, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbig h7.le]
    linarith
  have hfin := mul_le_mul_of_nonneg_right hmN hM0.le
  nlinarith


/-- **Chen's theorem above exp(exp t) from the three sieve bounds and a positive margin.** -/
theorem chenPos_of_sieveBounds (t : ℝ) (ht : 327 / 10 ≤ t) (κ : ℝ) (hκ : 0 ≤ κ) (cA cQ cB : ℕ → ℝ)
    (hA : Thm44At t cA) (hQ : Thm50At t cQ) (hB : Thm51At t cB) (hm : MarginKAt t κ cA cQ cB) :
    ChenPosAt t := by
  intro N hEven hNt
  have h := chenCount_gt_of_sieveBounds t ht κ cA cQ cB hA hQ hB hm N hEven hNt
  have hM0 : 0 ≤ mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  have : (0 : ℝ) < chenCount N := lt_of_le_of_lt (mul_nonneg hκ hM0) h
  exact_mod_cast this

#print axioms chenCount_gt_of_sieveBounds
#print axioms chenPos_of_sieveBounds

end LeanLab.ChenExplicit
