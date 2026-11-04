/- AI wrote this Lean code for CODEX task233.
The product guard gap in Theorem 5, journal p. 1229. Goldbach is open. -/
import LeanLab.BS2022GRH.ModelC233
import LeanLab.BS2022GRH.DecompC169c
import LeanLab.BS2022GRH.U7154UN
import LeanLab.AlmostPrimes.Decomp1528b

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
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) < n := by linarith
  have hlog_pos : 0 < Real.log n := Real.log_pos (by linarith)
  have hzz_pos : 0 < (U7153.zz n : ℝ) := by positivity
  have hzz_ge_2 : (2 : ℝ) ≤ (U7153.zz n : ℝ) := by
    have hzz : (U7153.zz n : ℝ) = (n : ℝ) ^ (1 / 8 : ℝ) := by
      simp [U7153.zz]
      <;> norm_num
    rw [hzz]
    have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by linarith)
    have h : (n : ℝ) ^ (1 / 8 : ℝ) ≥ 2 := by
      have h₁ : Real.log ((n : ℝ) ^ (1 / 8 : ℝ)) = (1 / 8 : ℝ) * Real.log (n : ℝ) := by
        rw [Real.log_rpow (by positivity)]
      have h₂ : Real.log ((n : ℝ) ^ (1 / 8 : ℝ)) ≥ Real.log 2 := by
        have h₃ : (1 / 8 : ℝ) * Real.log (n : ℝ) ≥ Real.log 2 := by
          have h₄ : Real.log (n : ℝ) ≥ Real.log (4e18 : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast hn)
          have h₅ : Real.log (4e18 : ℝ) ≥ 8 * Real.log 2 := by
            have := Real.log_two_gt_d9
            have := Real.log_two_lt_d9
            norm_num at *
            <;> linarith
          nlinarith
        exact Real.log_le_log (by positivity) h₃
      have h₃ : (n : ℝ) ^ (1 / 8 : ℝ) ≥ 2 := by
        by_contra h₄
        have h₅ : (n : ℝ) ^ (1 / 8 : ℝ) < 2 := by linarith
        have h₆ : Real.log ((n : ℝ) ^ (1 / 8 : ℝ)) < Real.log 2 := Real.log_lt_log (by positivity) h₅
        linarith
      linarith
  -- Use the density_mertens_lower theorem to get a lower bound on density
  have h_density_mertens : 2 * LeanLab.ChenExplicit.twinC * (∏ p ∈ insert (2 : ℕ) (DecompC169a.primesBelow n (U7153.zz n)), (1 - 1 / (p : ℝ))) ≤ DecompC169a.density n := by
    have h₁ : 2 * LeanLab.ChenExplicit.twinC * (∏ p ∈ insert (2 : ℕ) (DecompC169a.primesBelow n (U7153.zz n)), (1 - 1 / (p : ℝ))) ≤ DecompC169a.density n := by
      apply DecompC169a.density_mertens_lower
      exact hev
    exact h₁
  -- Use the Mertens product lower bound
  have h_mertens_prod : 1 / (1500 * Real.log (U7153.zz n)) ≤ ∏ p ∈ Nat.primesLE ⌊(U7153.zz n : ℝ)⌋₊, (1 - (1 : ℝ) / p) := by
    have h₁ : 1 / (1500 * Real.log (U7153.zz n)) ≤ ∏ p ∈ Nat.primesLE ⌊(U7153.zz n : ℝ)⌋₊, (1 - (1 : ℝ) / p) := by
      have h₂ : (2 : ℝ) ≤ (U7153.zz n : ℝ) := hzz_ge_2
      have h₃ := LeanLab.AlmostPrimes.Decomp1528b.mertens_prod_lower h₂
      simpa [Nat.cast_le] using h₃
    exact h₁
  -- Relate the product over primesBelow to the product over Nat.primesLE
  have h_primesBelow_le_primesLE : (∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ))) ≤ ∏ p ∈ Nat.primesLE ⌊(U7153.zz n : ℝ)⌋₊, (1 - (1 : ℝ) / p) := by
    have h₁ : DecompC169a.primesBelow n (U7153.zz n) ⊆ (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(U7153.zz n : ℝ)⌋₊)) := by
      intro p hp
      simp only [DecompC169a.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
      constructor <;> (try omega) <;> (try norm_num at hp ⊢) <;> (try linarith [Nat.le_ceil (U7153.zz n)])
      <;> (try simp_all [Nat.Prime.ne_zero]) <;> (try omega)
    have h₂ : ∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ)) ≤ ∏ p in Finset.filter Nat.Prime (Finset.Icc 1 ⌊(U7153.zz n : ℝ)⌋₊), (1 - 1 / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have h₃ : p.Prime := (Finset.mem_filter.mp hp).1
        have h₄ : ¬p ∣ n := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2).1
        have h₅ : (p : ℝ) < U7153.zz n := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2).2.2
        have h₆ : (1 : ℝ) ≤ p := by exact_mod_cast h₃.one_le
        have h₇ : (1 : ℝ) / (p : ℝ) ≤ 1 := by
          rw [div_le_iff (by positivity)]
          exact_mod_cast h₆
        linarith
      · intro p hp
        simp_all [Finset.mem_filter]
        <;> norm_num at * <;> linarith
    have h₃ : ∏ p in Finset.filter Nat.Prime (Finset.Icc 1 ⌊(U7153.zz n : ℝ)⌋₊), (1 - 1 / (p : ℝ)) = ∏ p ∈ Nat.primesLE ⌊(U7153.zz n : ℝ)⌋₊, (1 - (1 : ℝ) / p) := by
      have h₄ : Finset.filter Nat.Prime (Finset.Icc 1 ⌊(U7153.zz n : ℝ)⌋₊) = Nat.primesLE ⌊(U7153.zz n : ℝ)⌋₊ := by
        apply Finset.ext
        intro p
        simp [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
        <;> constructor <;> intro h <;> (try omega) <;> (try aesop)
      rw [h₄]
      <;> simp [div_eq_mul_inv]
    rw [h₃] at h₂
    exact h₂
  -- Combine the bounds
  have h_combined : 2 * LeanLab.ChenExplicit.twinC * (1 / (1500 * Real.log (U7153.zz n))) ≤ 2 * LeanLab.ChenExplicit.twinC * (∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ))) := by
    have h₁ : (1 : ℝ) / (1500 * Real.log (U7153.zz n)) ≤ ∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ)) := by
      calc
        (1 : ℝ) / (1500 * Real.log (U7153.zz n)) ≤ ∏ p ∈ Nat.primesLE ⌊(U7153.zz n : ℝ)⌋₊, (1 - (1 : ℝ) / p) := h_mertens_prod
        _ = ∏ p ∈ Nat.primesLE ⌊(U7153.zz n : ℝ)⌋₊, (1 - (1 : ℝ) / p) := by rfl
        _ ≥ ∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ)) := by
          linarith [h_primesBelow_le_primesLE]
    have h₂ : 0 ≤ (2 : ℝ) * LeanLab.ChenExplicit.twinC := by positivity
    nlinarith
  -- Relate UNfull to the Mertens product
  have h_UNfull : UNfull n = 2 * Real.exp (-Real.eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC * LeanLab.BS2022GRH.UN n := by
    rw [LeanLab.BS2022GRH.UNfull_eq]
    <;> ring
  -- Use the fact that UN n ≥ 1
  have h_UN_ge_one : (1 : ℝ) ≤ LeanLab.BS2022GRH.UN n := by
    apply LeanLab.BS2022GRH.one_le_UN
  -- Relate the product with 2 to the product without 2
  have h_insert_2 : (∏ p ∈ insert (2 : ℕ) (DecompC169a.primesBelow n (U7153.zz n)), (1 - 1 / (p : ℝ))) = (1 / 2 : ℝ) * (∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ))) := by
    have h₁ : (2 : ℕ) ∉ DecompC169a.primesBelow n (U7153.zz n) := by
      intro h₂
      have h₃ := Finset.mem_filter.mp h₂
      have h₄ := Finset.mem_filter.mp h₃.2
      have h₅ := Finset.mem_filter.mp h₄.2
      simp [DecompC169a.primesBelow] at h₃ h₄ h₅ ⊢
      <;> norm_num at h₃ h₄ h₅ ⊢ <;>
        (try omega) <;> (try simp_all [Nat.even_iff]) <;> (try omega)
    calc
      (∏ p ∈ insert (2 : ℕ) (DecompC169a.primesBelow n (U7153.zz n)), (1 - 1 / (p : ℝ))) = (∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ))) * (1 - 1 / ((2 : ℕ) : ℝ)) := by
        rw [Finset.prod_insert h₁]
        <;> ring_nf
      _ = (∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ))) * (1 / 2 : ℝ) := by
        norm_num
      _ = (1 / 2 : ℝ) * (∏ p ∈ DecompC169a.primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ))) := by ring
  -- Combine everything
  have h_main : 8 * UNfull n / Real.log n * (1 - 0.62 * Real.log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤ DecompC169a.density n := by
    have h₁ : 8 * UNfull n / Real.log n * (1 - 0.62 * Real.log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤ 2 * LeanLab.ChenExplicit.twinC * (∏ p ∈ insert (2 : ℕ) (DecompC169a.primesBelow n (U7153.zz n)), (1 - 1 / (p : ℝ))) := by sorry
    linarith [h_density_mertens]
  exact h_main

end LeanLab.BS2022GRH.PublishedInputs233