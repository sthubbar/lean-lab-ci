/- AI wrote the Lean code for CODEX task236.
Sieve assembly for journal Theorem 7. Goldbach is open. -/
import LeanLab.BS2022GRH.SliceSieve236
namespace LeanLab.BS2022GRH.SliceSieve236
open Real Finset Classical ChenThresholdGRH DecompC169a DecompC164c
noncomputable section
/-- The slice parameter is three halves minus three alpha, p. 1236 display 28. -/
theorem slice_parameter (n : ℕ) (α : ℝ) (hn : (1 : ℝ) < n) :
    log ((n : ℝ) ^ (1 / 2 - α)) / log (U7153.yy n) = 3 / 2 - 3 * α := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : log (n : ℝ) ≠ 0 := (log_pos hn).ne'
  rw [U7153.yy, log_rpow hn0, log_rpow hn0]
  field_simp

/-- The product cutoff comparison for the slice sieve, p. 1236.
CONDITIONAL ON Lemma 2. -/
theorem slice_cutoff (h2 : PaperInputs148.Lemma2J)
    (α A u X : ℝ) (n : ℕ) (hα : 0 < α) (hA : 0 < A)
    (hc : Cond25 α A u X) (hX : exp (exp 10) ≤ X) (hn : X ≤ (n : ℝ)) :
    (smallProduct n u : ℝ) * (n : ℝ) ^ (1 / 2 - α) ≤ √(n : ℝ) / log n ^ (A + 1) := by
  have hX1 : 1 < X := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX
  have hn0 : (0 : ℝ) < n := by linarith
  have hc19 : Cond19 α A u X :=
    ⟨(le_max_left _ _).trans hc.1, hc.2.1, hc.2.2.2.1, hc.2.2.2.2⟩
  have h19 := DecompC169b.cond19_at α A u X n hα hA hc19 hX1 hn
  have htheta := h2 u (by linarith [hc.2.2.2.1]) hc.2.2.2.2
  have hQ : (smallProduct n u : ℝ) ≤ exp u :=
    (DecompC169b.smallProduct_le_exp_theta n u).trans (exp_le_exp.mpr htheta)
  have hprod : (n : ℝ) ^ α * (n : ℝ) ^ (1 / 2 - α) = √(n : ℝ) := by
    rw [← rpow_add hn0]
    convert (sqrt_eq_rpow (n : ℝ)).symm using 1 <;> congr 1 <;> ring
  calc
    _ ≤ ((n : ℝ) ^ α / log n ^ (A + 1)) * (n : ℝ) ^ (1 / 2 - α) :=
      mul_le_mul_of_nonneg_right (hQ.trans h19) (rpow_nonneg hn0.le _)
    _ = _ := by rw [div_mul_eq_mul_div, hprod]

/-- The raw upper sieve coefficient is nonnegative, p. 1236 display 29. -/
theorem slice_coefficient_nonneg (α ε C₁ : ℝ) (hα : 0 < α) (hα1 : α < 1 / 16)
    (he : 0 < ε) (hC : 0 ≤ C₁) :
    0 ≤ 2 * exp eulerMascheroniConstant / (3 / 2 - 3 * α) + ε * C₁ := by
  have hs : 0 < 3 / 2 - 3 * α := by linarith
  positivity

/-- At this parameter exp squared times h equals one, p. 1237 display 29. -/
theorem slice_hS (α : ℝ) (hα : 0 < α) : exp 2 * hS (3 / 2 - 3 * α) = 1 := by
  unfold hS
  rw [if_pos (by linarith : (3 / 2 : ℝ) - 3 * α ≤ 2), ← exp_add]
  norm_num

/-- Scalar normalization of the factor three, p. 1236 display 29. -/
theorem coefficient_normalization (α ε C V L R M G : ℝ)
    (ha : (1 / 2 : ℝ) - α ≠ 0) (hL : L ≠ 0) :
    (2 * G / (3 / 2 - 3 * α) + ε * C) * (M * (3 * V / L * R)) =
      M * (V / L * R * (2 / (1 / 2 - α) * G + 3 * ε * C)) := by
  have hs : (3 / 2 : ℝ) - 3 * α = 3 * (1 / 2 - α) := by ring
  rw [hs]
  field_simp
  <;> ring

set_option maxHeartbeats 2000000 in
/-- The complete finite sieve reduction for Theorem 7, pp. 1236 and 1237.
CONDITIONAL ON Lemmas 2 and 7 and the upper product estimate of Lemma 10. -/
theorem sieve_slices_of_inputs (α A u ε C₁ C₂ X₂ ε₁ : ℝ) (n : ℕ)
    (hT : LinearSieveT4 ε C₁ C₂) (hL : Lemma7J) (h2 : PaperInputs148.Lemma2J)
    (hC₁ : 0 ≤ C₁) (heps : epsJ u ≤ ε) (he0 : 0 < ε) (he1 : ε < 1 / 63)
    (hε₁ : 0 < ε₁) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n)
    (hdensity : (∏ p ∈ primesBelow n (U7153.yy n), (1 - 1 / ((p : ℝ) - 1))) ≤
      3 * UNfull n / log n * (1 + 0.06 * log n / (n : ℝ) ^ (1 / 6 : ℝ))) :
    (U7153.SB n : ℝ) ≤ mass n ε₁ * sieveCoefficient n α ε C₁ + DecompC164c.remainder n A ε₁ := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le (hX.trans hn)
  have hnN : 0 < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le (hX.trans hn)
  have hlog : 0 < log (n : ℝ) := log_pos hn1
  have hyexp := y_gt_exp2753 n (hX.trans hn)
  have hexp : (1e8 : ℝ) < exp 2753 := by
    have h := pow_div_factorial_le_exp (x := (2753 : ℝ)) (by norm_num) 3
    norm_num [Nat.factorial] at h
    linarith
  have hy : 2 ≤ U7153.yy n := by linarith
  have huz : u < U7153.yy n := by linarith [hc.2.2.2.2]
  have hprod := product_guard n (U7153.yy n) u ε hL hyexp hc.2.2.2.1 huz heps he0
  have hyD : U7153.yy n ≤ (n : ℝ) ^ (1 / 2 - α) :=
    rpow_le_rpow_of_exponent_le hn1.le (by linarith : (1 / 3 : ℝ) ≤ 1 / 2 - α)
  have hs3 : log ((n : ℝ) ^ (1 / 2 - α)) / log (U7153.yy n) ≤ 3 := by
    rw [slice_parameter n α hn1]
    linarith
  have hcut := slice_cutoff h2 α A u X₂ n hα hA hc hX hn
  apply sieve_slices_of_pointwise n α ε C₁ A ε₁ hnN hε₁
  intro j hj
  have hraw := slice_sieve_raw n j A ε₁ ((n : ℝ) ^ (1 / 2 - α)) u ε C₁ C₂
    hT hev he0 he1 hy hprod hyD hs3 hcut
  rw [slice_parameter n α hn1] at hraw
  have hh : ε * C₁ * exp 2 * hS (3 / 2 - 3 * α) = ε * C₁ := by
    rw [mul_assoc (ε * C₁), slice_hS α hα, mul_one]
  rw [hh] at hraw
  have hco := slice_coefficient_nonneg α ε C₁ hα hα1 he0 hC₁
  have hsne : (3 / 2 : ℝ) - 3 * α ≠ 0 := by linarith
  have hane : (1 / 2 : ℝ) - α ≠ 0 := by linarith
  have hnorm : (2 * exp eulerMascheroniConstant / (3 / 2 - 3 * α) + ε * C₁) *
      (((slice n ε₁ j).card : ℝ) * (3 * UNfull n / log n *
        (1 + 0.06 * log n / (n : ℝ) ^ (1 / 6 : ℝ)))) =
      ((slice n ε₁ j).card : ℝ) * sieveCoefficient n α ε C₁ := by
    exact coefficient_normalization α ε C₁ (UNfull n) (log n)
      (1 + 0.06 * log n / (n : ℝ) ^ (1 / 6 : ℝ))
      ((slice n ε₁ j).card : ℝ) (exp eulerMascheroniConstant) hane hlog.ne'
  calc
    _ ≤ _ := hraw
    _ ≤ (2 * exp eulerMascheroniConstant / (3 / 2 - 3 * α) + ε * C₁) *
        (((slice n ε₁ j).card : ℝ) * (3 * UNfull n / log n *
          (1 + 0.06 * log n / (n : ℝ) ^ (1 / 6 : ℝ)))) +
        ∑ d ∈ divisors n A, |residueError n ε₁ j d| :=
      add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg _)) hco) le_rfl
    _ = _ := by rw [hnorm]

end
end LeanLab.BS2022GRH.SliceSieve236

#print axioms LeanLab.BS2022GRH.SliceSieve236.slice_parameter
#print axioms LeanLab.BS2022GRH.SliceSieve236.slice_cutoff
#print axioms LeanLab.BS2022GRH.SliceSieve236.slice_coefficient_nonneg
#print axioms LeanLab.BS2022GRH.SliceSieve236.slice_hS
#print axioms LeanLab.BS2022GRH.SliceSieve236.coefficient_normalization
#print axioms LeanLab.BS2022GRH.SliceSieve236.sieve_slices_of_inputs
