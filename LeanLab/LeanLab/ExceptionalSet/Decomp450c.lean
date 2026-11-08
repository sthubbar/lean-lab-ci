import LeanLab.ExceptionalSet.Decomp446c

/-!
Scalar consequences of the application of Theorem 2 on P0082 page 366.
Source: https://doi.org/10.5802/aif.1621
The constants are auxiliary margins used in the existing formal decomposition.
No new cancellation or cited analytic input is assumed.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450c

open Real Filter
open LeanLab.ExceptionalSet.U1539 (calE)

/-- P0082 page 366, auxiliary control of the dyadic half index.
This is the exact scalar leaf in SPLIT_leaf_decay_rescale. -/
theorem log_half_quarter (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ N : ℕ, 64 ≤ N →
      (1 / 4) * Real.log (N : ℝ) ^ a ≤ Real.log (N / 2 : ℕ) ^ a := by
  intro N hN
  have hk : 32 ≤ N / 2 := by omega
  have hk' : (32 : ℝ) ≤ (N / 2 : ℕ) := by exact_mod_cast hk
  have hd : N ≤ 2 * (N / 2) + 1 := by omega
  have hd' : (N : ℝ) ≤ 2 * (N / 2 : ℕ) + 1 := by exact_mod_cast hd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hsquare : (N : ℝ) ≤ ((N / 2 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hl : Real.log (N : ℝ) ≤ 2 * Real.log (N / 2 : ℕ) := by
    calc
      _ ≤ Real.log (((N / 2 : ℕ) : ℝ) ^ 2) := Real.log_le_log hNpos hsquare
      _ = _ := by rw [Real.log_pow]; norm_num
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (1 / 2 : ℝ) * Real.log (N : ℝ))
    (by linarith : (1 / 2 : ℝ) * Real.log (N : ℝ) ≤ Real.log (N / 2 : ℕ)) ha0.le
  rw [Real.mul_rpow (by norm_num) hlog] at hp
  have hc : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ a := by
    have hc := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) ha1.le
    rw [Real.rpow_one] at hc
    linarith
  exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hlog a)).trans hp

/-- P0082 page 366, the dyadic logarithm comparison carried through the exponential. -/
theorem exp_decay_quarter (γ η : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hη : 0 < η) :
    ∀ N : ℕ, 64 ≤ N →
      Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) ≤
        Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
  intro N hN
  apply Real.exp_le_exp.mpr
  have hh := log_half_quarter (3 - 2 * γ) (by linarith) (by linarith) N hN
  nlinarith

/-- P0082 page 366, auxiliary explicit kappa cap for the calE scale. -/
theorem calE_kappa_comparison (γ η κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hη : 0 < η) (hκ : 0 < κ) (hκ6 : κ ≤ η / 6) (N : ℕ) (hN : 64 ≤ N) :
    Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤ calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  rw [calE, ← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hp : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg hlog _
  nlinarith

/-- P0082 page 366, auxiliary sublinear growth used to absorb absolute endpoint errors. -/
theorem exp_log_pow_le (γ η : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.exp (η * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤ (N : ℝ) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 - (3 - 2 * γ))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - (3 - 2 * γ))).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop η)
  refine ⟨max 2 N₀, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp := mul_le_mul_of_nonneg_left (hN₀ N ((le_max_right _ _).trans hN))
    (Real.rpow_nonneg hlog.le (3 - 2 * γ))
  rw [← Real.rpow_add hlog] at hp
  have he : (3 - 2 * γ) + (1 - (3 - 2 * γ)) = 1 := by ring
  rw [he, Real.rpow_one] at hp
  calc
    _ ≤ Real.exp (Real.log (N : ℝ)) := Real.exp_le_exp.mpr (by nlinarith [hp])
    _ = _ := Real.exp_log hNpos

/-- P0082 page 366, scalar bookkeeping for the two absolute endpoint errors. -/
theorem arith_bookkeeping (B : ℝ) (N : ℕ) (e Y : ℝ) (hB : 0 < B) (he : e ≤ Y)
    (hNY : 1 ≤ (N : ℝ) * Y) :
    B * (N / 2 : ℕ) * e + 2 ≤ (2 * B + 2) * (N : ℝ) * Y := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hY : 0 ≤ Y := by
    by_contra hy
    have hn := mul_nonpos_of_nonneg_of_nonpos hN (le_of_not_ge hy)
    linarith
  have hhalf : ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N 2
  have hfirst : B * (N / 2 : ℕ) * e ≤ B * (N / 2 : ℕ) * Y :=
    mul_le_mul_of_nonneg_left he (by positivity)
  have hsecond : B * (N / 2 : ℕ) * Y ≤ B * N * Y := by gcongr
  have hBN := mul_le_mul_of_nonneg_left hNY hB.le
  nlinarith

/-- P0082 page 366, exact inherited scalar rescaling leaf with no cited analytic input. -/
theorem decay_rescale_supplied (γ η B : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hη : 0 < η) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ κ : ℝ, 0 < κ → κ ≤ η / 6 →
      ∀ N : ℕ, N₀ ≤ N →
        B * (N / 2 : ℕ) * Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) + 2 ≤
          C * N * calE γ κ N ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨Ne, he⟩ := exp_log_pow_le γ (η / 4) h1 h2 (by positivity)
  refine ⟨2 * B + 2, by linarith, max 64 Ne, fun κ hκ hκ6 N hN => ?_⟩
  have hN64 : 64 ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hX : Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) ≤
      calE γ κ N ^ (-(3 / 2 : ℝ)) :=
    (exp_decay_quarter γ η h1 h2 hη N hN64).trans
      (calE_kappa_comparison γ η κ h1 h2 hη hκ hκ6 N hN64)
  have hquarter : (1 : ℝ) / Real.exp (η / 4 * Real.log (N : ℝ) ^ (3 - 2 * γ))
      = Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hinv : (1 : ℝ) / (N : ℝ) ≤
      Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    rw [← hquarter]
    exact one_div_le_one_div_of_le (Real.exp_pos _) (he N hNe)
  have hNY : 1 ≤ (N : ℝ) * calE γ κ N ^ (-(3 / 2 : ℝ)) := by
    have hlin : (1 : ℝ) ≤
        (N : ℝ) * Real.exp (-(η / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
      have hmul := mul_le_mul_of_nonneg_left hinv hNpos.le
      rwa [mul_one_div, div_self (ne_of_gt hNpos)] at hmul
    exact hlin.trans (mul_le_mul_of_nonneg_left
      (calE_kappa_comparison γ η κ h1 h2 hη hκ hκ6 N hN64) hNpos.le)
  exact arith_bookkeeping B N _ _ hB hX hNY

end LeanLab.ExceptionalSet.Decomp450c
