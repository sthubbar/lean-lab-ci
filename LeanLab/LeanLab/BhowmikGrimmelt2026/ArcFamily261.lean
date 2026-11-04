/-
Actual smoothing family estimates retaining the full Lemma 7.2 remainder.
Source: P0029 pages 26 and 27, displays 7.5 and 7.8.
The original two family leaves remain sealed and open.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.WeightedFamily261
import LeanLab.BhowmikGrimmelt2026.Decomp150d
import LeanLab.BhowmikGrimmelt2026.Lemma72Proof

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Major family estimate with the full Poisson remainder and the actual smoothing scales. -/
theorem major_family_remainder261 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ R η : ℝ,
      1 ≤ R → 0 < η → η ≤ 1 → 10 * R ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, if MajorArc X R α then
          Sphi ϕ N α ^ 2 * (1 - bRhat G R (fun q => η * X * q / R) α) *
            ee (-(N * α)) else 0‖ ^ 2 ≤
          C * (η ^ 2 + R ^ 2 * (η * X / R ^ 2) ^ (-A)) ^ 2 *
            (X : ℝ) ^ 3 * Real.log X := by
  obtain ⟨Cφ, hCφ, hfamily⟩ := smoothed_family_bound261 hϕ
  obtain ⟨D, hD⟩ := lemma72 G hG A hA
  let D' : ℝ := max D 1
  have hD' : 0 ≤ D' := le_trans (by norm_num) (le_max_right D 1)
  refine ⟨Cφ * D' ^ 2, by positivity, ?_⟩
  intro X hX R η hR hη hη1 hscale
  have hRpos : 0 < R := by linarith
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hT : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < η * X * q / R := by
    intro q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    positivity
  let W : ℝ → ℂ := fun α => if MajorArc X R α then
    1 - bRhat G R (fun q => η * X * q / R) α else 0
  let E : ℝ := η ^ 2 + R ^ 2 * (η * X / R ^ 2) ^ (-A)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hW : Measurable W :=
    ((continuous_const.sub (continuous_bRhat hG.supp hG.even R _ hT)).measurable).ite
      (measurableSet_majorArc84 X R) measurable_const
  have hWB (α : ℝ) : ‖W α‖ ≤ D' * E := by
    by_cases hm : MajorArc X R α
    · dsimp [W]
      rw [if_pos hm, norm_sub_rev]
      exact ((hD X R η hR hη hη1 hscale α).1 hm).trans
        (mul_le_mul_of_nonneg_right (le_max_left D 1) hE)
    · simp only [W, if_neg hm, norm_zero]
      positivity
  have h := hfamily X hX W hW (D' * E) (mul_nonneg hD' hE) hWB
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, if MajorArc X R α then
        Sphi ϕ N α ^ 2 * (1 - bRhat G R (fun q => η * X * q / R) α) *
          ee (-(N * α)) else 0) =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases hm : MajorArc X R α <;> simp [W, hm]
  simp_rw [heq]
  convert h using 1 <;> dsimp [E] <;> ring

/-- A negligible Poisson remainder suffices for the major family bound with log power one. -/
theorem major_family_of_tail261 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ R η : ℝ,
      1 ≤ R → 0 < η → η ≤ 1 → 10 * R ^ 2 ≤ η * X →
      R ^ 2 * (η * X / R ^ 2) ^ (-A) ≤ η ^ 2 →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, if MajorArc X R α then
          Sphi ϕ N α ^ 2 * (1 - bRhat G R (fun q => η * X * q / R) α) *
            ee (-(N * α)) else 0‖ ^ 2 ≤
          C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by
  obtain ⟨C, hC, hbound⟩ := major_family_remainder261 hϕ hG A hA
  refine ⟨4 * C, by positivity, ?_⟩
  intro X hX R η hR hη hη1 hscale htail
  apply (hbound X hX R η hR hη hη1 hscale).trans
  have hsum : 0 ≤ η ^ 2 + R ^ 2 * (η * X / R ^ 2) ^ (-A) := by positivity
  have hs := pow_le_pow_left₀ hsum (by linarith :
    η ^ 2 + R ^ 2 * (η * X / R ^ 2) ^ (-A) ≤ 2 * η ^ 2) 2
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  nlinarith [mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ C * (X : ℝ) ^ 3 * Real.log X)]

/-- At the paper's optimized eta a fixed decay exponent absorbs the Poisson remainder. -/
theorem optimized_tail261 {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ' : ϑ < 4 / 9) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 < x →
      (x ^ ϑ) ^ 2 * ((x ^ ϑ) ^ (-(1 / 4) : ℝ) * x / (x ^ ϑ) ^ 2) ^ (-A) =
        ((x ^ ϑ) ^ (-(1 / 4) : ℝ)) ^ 2 := by
  let d : ℝ := 1 - 9 * ϑ / 4
  have hd : 0 < d := by dsimp [d]; linarith
  refine ⟨(5 * ϑ / 2) / d, div_pos (by positivity) hd, ?_⟩
  intro x hx
  have hR : (x ^ ϑ) ^ 2 = x ^ (2 * ϑ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hη : (x ^ ϑ) ^ (-(1 / 4) : ℝ) = x ^ (-ϑ / 4) := by
    rw [← Real.rpow_mul hx.le]
    congr 1
    ring
  have hK : (x ^ ϑ) ^ (-(1 / 4) : ℝ) * x / (x ^ ϑ) ^ 2 = x ^ d := by
    rw [hR, hη]
    calc
      _ = x ^ (-ϑ / 4) * x ^ (1 : ℝ) / x ^ (2 * ϑ) := by rw [Real.rpow_one]
      _ = x ^ (-ϑ / 4 + 1 - 2 * ϑ) := by rw [← Real.rpow_add hx, ← Real.rpow_sub hx]
      _ = _ := by congr 1; dsimp [d]; ring
  rw [hK, hR, hη, ← Real.rpow_mul hx.le, ← Real.rpow_add hx,
    ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  field_simp
  <;> ring

/-- The optimized major contribution in display 7.9, with the actual N dependent smoothing. -/
theorem major_family_optimized261 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 4 / 9) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖majorError150 ϕ G X N ϑ (((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ))‖ ^ 2 ≤
          C * (X : ℝ) ^ (3 - ϑ) * Real.log X := by
  obtain ⟨A, hA, htail⟩ := optimized_tail261 hϑ hϑ'
  obtain ⟨C, hC, hbound⟩ := major_family_of_tail261 hϕ hG A hA
  refine ⟨C, hC, ?_⟩
  intro X hX hscale
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hRpos : 0 < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hXpos ϑ
  have hηpos : 0 < ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hRpos _
  have hη1 : ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR1 (by norm_num)
  have hb := hbound X hX ((X : ℝ) ^ ϑ) (((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ))
    hR1 hηpos hη1 hscale (htail X hXpos).le
  have hpow : (((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ)) ^ 4 * (X : ℝ) ^ 3 =
      (X : ℝ) ^ (3 - ϑ) := by
    rw [← Real.rpow_natCast (((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ)) 4,
      ← Real.rpow_mul hRpos.le]
    norm_num
    rw [← Real.rpow_mul hXpos.le, ← Real.rpow_natCast (X : ℝ) 3,
      ← Real.rpow_add hXpos]
    congr 1
    ring
  simpa only [majorError150, mul_assoc, hpow] using hb

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.major_family_remainder261
#print axioms LeanLab.BhowmikGrimmelt2026.major_family_of_tail261

#print axioms LeanLab.BhowmikGrimmelt2026.optimized_tail261
#print axioms LeanLab.BhowmikGrimmelt2026.major_family_optimized261
