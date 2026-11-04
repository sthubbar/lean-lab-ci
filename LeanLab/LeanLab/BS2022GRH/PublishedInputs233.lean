/- AI wrote this Lean code for CODEX task233.
The product guard gap in Theorem 5, journal p. 1229. Goldbach is open. -/
import LeanLab.BS2022GRH.ModelC233
import LeanLab.BS2022GRH.DecompC169c

namespace LeanLab.BS2022GRH.PublishedInputs233
open Real Finset ChenThresholdGRH

/-- Row 37 of Table 15 controls the reciprocal sum already above exp 400.
Journal pp. 1219 to 1221. CONDITIONAL ON the stated theta estimate. -/
theorem reciprocal_upper_exp400 (M : ℝ)
    (hlim : Filter.Tendsto (fun y : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) - log (log y)) Filter.atTop (nhds M))
    (hθ : ∀ t : ℝ, exp 37 < t →
      |Chebyshev.theta t - t| ≤ (8.6315e-7 : ℝ) * t / log t)
    (z : ℝ) (hz : exp 400 < z) :
    (∑ p ∈ Nat.primesBelow ⌈z⌉₊, (1 : ℝ) / p) ≤ log (log z) + M + 2.166e-9 := by
  have hz2 : 2 ≤ z := by linarith [add_one_le_exp (400 : ℝ)]
  have hL : 400 < log z := by
    have h := log_lt_log (exp_pos 400) hz
    simpa only [log_exp] using h
  have htail : ∀ t : ℝ, z ≤ t →
      |Chebyshev.theta t - t| ≤ (8.6315e-7 : ℝ) * t / log t := by
    intro t ht
    exact hθ t (((exp_lt_exp.mpr (by norm_num : (37 : ℝ) < 400)).trans hz).trans_le ht)
  have hu := ThetaMertens224.reciprocal_upper_from_theta M 8.6315e-7 hlim hz2 htail
  have h1 : (8.6315e-7 : ℝ) / log z ≤ 8.6315e-7 / 400 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL.le
  have h2 : (3 : ℝ) / (2 * log z) ≤ 3 / (2 * 400) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have herr : (8.6315e-7 : ℝ) / log z * (1 + 3 / (2 * log z)) ≤ 2.166e-9 := by
    calc
      _ ≤ (8.6315e-7 / 400 : ℝ) * (1 + 3 / (2 * 400)) :=
        mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
      _ ≤ _ := by norm_num
  have hgap := (DecompC169c.reciprocal_endpoint_gap z hz2).1
  linarith

/-- The product argument only needs the reciprocal band estimate, p. 1222.
CONDITIONAL ON the displayed reciprocal sum bound. -/
theorem product_of_reciprocal (z u₀ v : ℝ) (hu : 400 ≤ u₀) (huv : u₀ ≤ v) (hvz : v < z)
    (h9 : ∑ p ∈ Decomp138.band v z, (1 : ℝ) / p <
      log (log z) - log (log v) + 1.131e-7) :
    (∏ p ∈ Decomp138.band v z, (1 - 1 / ((p : ℝ) - 1))⁻¹) <
      (1 + epsJ u₀) * (log z / log v) := by
  rw [Decomp138.product_split z v (hu.trans huv)]
  have hnonneg : 0 ≤ ∏ p ∈ Decomp138.band v z, (1 - 1 / (p : ℝ))⁻¹ := by
    apply prod_nonneg
    intro p hp
    have hpv := (mem_filter.mp hp).2.2.1
    have hp0 : 0 < (p : ℝ) := by linarith
    have hp1 : 1 / (p : ℝ) < 1 := (div_lt_one hp0).mpr (by linarith)
    positivity
  calc
    _ ≤ exp (u₀ / (u₀ - 2) * Decomp138.squareTail u₀) *
        ∏ p ∈ Decomp138.band v z, (1 - 1 / (p : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right (Decomp138.correction_product_le z u₀ v hu huv) hnonneg
    _ < exp (u₀ / (u₀ - 2) * Decomp138.squareTail u₀) *
        (exp (1.131e-7 + 0.501 * Decomp138.squareTail u₀) * (log z / log v)) :=
      mul_lt_mul_of_pos_left (Decomp138.mertens_product_lt z u₀ v hu huv hvz h9) (exp_pos _)
    _ = _ := by
      rw [← mul_assoc, ← exp_add]
      unfold epsJ Decomp138.squareTail
      congr 1
      ring_nf

/-- LEAF. Product guard invoked on journal p. 1229 after display 19.
QUESTION. Lemma 7 on p. 1221 only covers z greater than exp 2753.
This is the missing smaller-level input, not a proved consequence of Lemma 7. -/
theorem small_level_product (z u₀ v : ℝ)
    (hz : exp 400 < z) (hzmax : z ≤ exp 2753)
    (hu : 400 ≤ u₀) (huv : u₀ ≤ v) (hvz : v < z) :
    (∏ p ∈ (range ⌈z⌉₊).filter
      (fun p : ℕ => p.Prime ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - 1 / ((p : ℝ) - 1))⁻¹) <
        (1 + epsJ u₀) * (log z / log v) := by
  have hupper := reciprocal_upper_exp400 DecompC169c.mertensConstant
    DecompC169c.reciprocal_limit ThetaInputs224.theta_table15_37 z hz
  have hv400 : 400 ≤ v := hu.trans huv
  have hlower : log (log v) + DecompC169c.mertensConstant - 1.107533e-7 ≤
      ∑ p ∈ Nat.primesBelow ⌈v⌉₊, (1 : ℝ) / p := by
    by_cases hsmall : v ≤ 1e12
    · have h := DecompC169c.reciprocal_lower_finite v (by linarith) hsmall
      linarith
    · exact DecompC169c.reciprocal_lower_infinite v (lt_of_not_ge hsmall)
  have h9 : ∑ p ∈ Decomp138.band v z, (1 : ℝ) / p <
      log (log z) - log (log v) + 1.131e-7 := by
    rw [Mertens138.sum_band_eq_sub v z hvz.le]
    linarith
  exact product_of_reciprocal z u₀ v hu huv hvz h9

/-- LEAF. Lower finite prime product estimate from journal Lemma 10, p. 1227.
Use the lab normalization UNfull, the full Mertens constant with factor two.
The printed journal UN omits that factor, as recorded in U7154UN. -/
theorem density_lower (n : ℕ) (hG : GRH) (hn : (4e18 : ℝ) ≤ n) (hev : Even n) :
    8 * UNfull n / log n * (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤
      DecompC169a.density n := by
  sorry

end LeanLab.BS2022GRH.PublishedInputs233
