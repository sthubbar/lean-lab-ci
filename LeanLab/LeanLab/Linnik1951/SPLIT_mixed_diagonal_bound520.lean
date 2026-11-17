/-
Split of the sealed open leaf `mixed_diagonal_bound520` of
`LeanLab.Linnik1951.SPLIT_mixed_bound520`.

The diagonal contribution is the signed Ramanujan sum of the residual frequency
times the centred square of the principal prime series, integrated over one
centred local arc of radius one over q times N to the one seventh.

The estimate is cut into two statements:

* the short arc size of the principal square, which is the analytic input and
  makes no reference to the signed Ramanujan sum;
* the absorption of that size into the display of the target, which only uses
  that the modulus is at most the tenth root of the scale.

The assembly multiplies by the elementary size bound for the signed Ramanujan
sum, at most the number of reduced residues below the modulus, and cancels the
modulus against the arc radius.
-/
import LeanLab.Linnik1951.SPLIT_mixed_bound520

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- Auxiliary elementary bound: every term of the signed Ramanujan sum is a
phase of unit modulus, so the sum is at most the number of reduced residues
below the modulus, and that number is at most the modulus itself. -/
private lemma ramanujan_norm_le_card520 (q : ℕ) (n : ℤ) :
    ‖signedRamanujan520 q n‖ ≤ (q : ℝ) := by
  classical
  unfold signedRamanujan520
  calc ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
    _ = ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), (1 : ℝ) :=
        Finset.sum_congr rfl (fun a _ => Complex.norm_exp_ofReal_mul_I _)
    _ = (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) := by simp
    _ ≤ (q : ℝ) := by
        have hc : ((range q).filter (fun a => Nat.Coprime a q)).card ≤ q := by
          have h := Finset.card_filter_le (range q) (fun a => Nat.Coprime a q)
          simpa using h
        exact_mod_cast hc

/-- LEAF. Short arc size of the principal square. The squared principal prime
series, weighted by the central phase, integrates over one centred arc of
radius one over q times N to the one seventh to at most the scale N times the
third power of the logarithm of N, divided by the modulus times N to the one
seventh. This is the analytic input of the diagonal estimate, and it makes no
reference to the signed Ramanujan sum. -/
theorem principal_square_short_arc520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖principalIntegral520 N q n‖ ≤
        C * (N : ℝ) * Real.log N ^ 3 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. Absorption of the size into the display of the target. For a modulus
at most the tenth root of the scale, the bound just obtained, with the modulus
cancelled, is at most a constant multiple of the display of the target: the
square root of the modulus is smaller than the fourteenth root of the scale
times the third power of the logarithm. -/
theorem diag_scale_absorption520 :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
      (N : ℝ) * Real.log N ^ 3 / (N : ℝ) ^ (1 / 7 : ℝ) ≤
        K * ((N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  refine ⟨1, one_pos, 2, ?_⟩
  intro N hN q hq hqQ
  have hN3 : 3 ≤ N := by omega
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hA0 : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hs0 : (0 : ℝ) < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    Real.sqrt_pos.2 (mul_pos hq0 hA0)
  have hlog1 : 1 ≤ Real.log N := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      have hle : Real.log (Real.exp 1) ≤ Real.log 3 :=
        (Real.log_le_log_iff (Real.exp_pos 1) (by norm_num)).mpr Real.exp_one_lt_three.le
      simpa [Real.log_exp] using hle
    have hle : Real.log 3 ≤ Real.log N :=
      (Real.log_le_log_iff (by norm_num) hN0).mpr (by exact_mod_cast hN3)
    linarith
  have hlog0 : 0 < Real.log N := by linarith
  -- the square root of the modulus times the arc denominator is at most the arc
  -- denominator times the cube of the logarithm
  have hsq : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
      (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 3 := by
    have hprod : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) =
        Real.sqrt (q : ℝ) * Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) :=
      Real.sqrt_mul hq0.le _
    have hq20 : Real.sqrt (q : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) := by
      have hle : Real.sqrt (q : ℝ) ≤ Real.sqrt ((N : ℝ) ^ (1 / 10 : ℝ)) :=
        Real.sqrt_le_sqrt hqQ
      have he : Real.sqrt ((N : ℝ) ^ (1 / 10 : ℝ)) = (N : ℝ) ^ (1 / 20 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
        norm_num
      rwa [he] at hle
    have hN14 : Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) = (N : ℝ) ^ (1 / 14 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
      norm_num
    have hN20pos : (0 : ℝ) < (N : ℝ) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hN0 _
    have hprod2 : Real.sqrt (q : ℝ) * Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) ≤
        (N : ℝ) ^ (1 / 20 : ℝ) * (N : ℝ) ^ (1 / 14 : ℝ) := by
      refine mul_le_mul hq20 ?_ (Real.sqrt_nonneg _) hN20pos.le
      rw [hN14]
    have hsum : (N : ℝ) ^ (1 / 20 : ℝ) * (N : ℝ) ^ (1 / 14 : ℝ) =
        (N : ℝ) ^ (17 / 140 : ℝ) := by
      rw [← Real.rpow_add hN0]
      norm_num
    have hsmall : (N : ℝ) ^ (17 / 140 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have hlog3 : 1 ≤ Real.log N ^ 3 := one_le_pow₀ hlog1
    calc Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
        = Real.sqrt (q : ℝ) * Real.sqrt ((N : ℝ) ^ (1 / 7 : ℝ)) := hprod
      _ ≤ (N : ℝ) ^ (1 / 20 : ℝ) * (N : ℝ) ^ (1 / 14 : ℝ) := hprod2
      _ = (N : ℝ) ^ (17 / 140 : ℝ) := hsum
      _ ≤ (N : ℝ) ^ (1 / 7 : ℝ) := hsmall
      _ ≤ (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 3 := by
          nth_rewrite 1 [← mul_one ((N : ℝ) ^ (1 / 7 : ℝ))]
          exact mul_le_mul_of_nonneg_left hlog3 hA0.le
  rw [one_mul, div_le_div_iff₀ hA0 hs0]
  have hmul : (N : ℝ) * Real.log N ^ 3 * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
      (N : ℝ) * Real.log N ^ 3 * ((N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 3) :=
    mul_le_mul_of_nonneg_left hsq (mul_nonneg hN0.le (pow_nonneg hlog0.le 3))
  refine le_trans hmul (le_of_eq ?_)
  ring

/-- The sealed statement, obtained from the two leaves by the elementary size
bound for the signed Ramanujan sum and by cancelling the modulus against the
arc radius. -/
theorem mixed_diagonal_bound520_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖signedRamanujan520 q n *
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
 := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := principal_square_short_arc520 hG
  obtain ⟨K, hK, N₂, h₂⟩ := diag_scale_absorption520
  refine ⟨C₁ * K, mul_pos hC₁ hK, max N₁ (max N₂ 2), ?_⟩
  intro N hN q hq hqQ n hn
  have hidx₁ : N₁ ≤ max N₁ (max N₂ 2) := le_max_left _ _
  have hidx₂ : N₂ ≤ max N₁ (max N₂ 2) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hidx₃ : 2 ≤ max N₁ (max N₂ 2) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hN₁ : N₁ < N := lt_of_le_of_lt hidx₁ hN
  have hN₂ : N₂ < N := lt_of_le_of_lt hidx₂ hN
  have hN2 : 2 < N := lt_of_le_of_lt hidx₃ hN
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN7 : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNr _
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq0
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNr
  have hN7ne : (N : ℝ) ^ (1 / 7 : ℝ) ≠ 0 := ne_of_gt hN7
  have hdef : (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
      principalPrime520 N q z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))
      = principalIntegral520 N q n := rfl
  rw [hdef]
  have hS : ‖signedRamanujan520 q n‖ ≤ (q : ℝ) := ramanujan_norm_le_card520 q n
  have hI := h₁ N hN₁ q hq hqQ n hn
  have hA := h₂ N hN₂ q hq hqQ
  have hstep : ‖signedRamanujan520 q n‖ * ‖principalIntegral520 N q n‖ ≤
      (q : ℝ) * (C₁ * (N : ℝ) * Real.log N ^ 3 /
        ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    mul_le_mul hS hI (norm_nonneg _) hq0.le
  have hqmul : (q : ℝ) * (C₁ * (N : ℝ) * Real.log N ^ 3 /
        ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))
      = C₁ * ((N : ℝ) * Real.log N ^ 3 / (N : ℝ) ^ (1 / 7 : ℝ)) := by
    field_simp
  calc ‖signedRamanujan520 q n * principalIntegral520 N q n‖
      = ‖signedRamanujan520 q n‖ * ‖principalIntegral520 N q n‖ := norm_mul _ _
    _ ≤ (q : ℝ) * (C₁ * (N : ℝ) * Real.log N ^ 3 /
          ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := hstep
    _ = C₁ * ((N : ℝ) * Real.log N ^ 3 / (N : ℝ) ^ (1 / 7 : ℝ)) := hqmul
    _ ≤ C₁ * (K * ((N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hA hC₁.le
    _ = (C₁ * K) * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by ring

end LeanLab.Linnik1951
