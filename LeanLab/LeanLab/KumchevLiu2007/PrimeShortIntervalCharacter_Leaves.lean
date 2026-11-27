/-
Kumchev and Liu 2007, arXiv 0801.0130, P0088, page 15, first paragraph of
Section 4: the prime indicator satisfies hypothesis A1.2 of page 5 with
f1 u = 1 / log u, "a short interval form of the Siegel Walfisz theorem that can
be established by the same methods as Huxley's theorem on primes in short
intervals".

This file splits the two true leaves of
`SPLIT_prime_short_interval_character.lean`, namely
`leaf_nonprincipal_prime_character_sum` and
`leaf_principal_prime_count_level_one`, into five smaller leaves along the
standard route the paper names:

* two HARD analytic inputs, both von Mangoldt weighted: the short interval
  Siegel Walfisz bound for a nonprincipal character and Huxley's prime number
  theorem in short intervals;
* three MEDIUM elementary steps: the prime powers that are not primes carry a
  negligible von Mangoldt mass in the window, the weight `1 / log p` may be
  swapped for `1 / log X` on the window, and the same swap on all integers.

The two theorems `..._from_leaves` restate the two parent leaves exactly and
are proved from the five leaves with no open step of their own.

The third parent leaf, `leaf_principal_prime_count_level_exceeding_one`, is
false as cut and is refuted on main by
`principal_prime_count_level_exceeding_one_fails`; it is not split here.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556a
import LeanLab.KumchevLiu2007.Kernel634Base
import Mathlib.NumberTheory.Chebyshev

namespace LeanLab.KumchevLiu2007.Task556a

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Derived elementary estimate for P0088 page 15, the passage to the reciprocal logarithm prime model. -/
theorem psc_tail_log_absorb (B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      2 * Real.sqrt X * Real.log X ≤
        windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  let d : ℝ := 7 / 12 + ε / 2 - 1 / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have ht := (isLittleO_log_rpow_rpow_atTop (1 + 5 * B) hd).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [ht, Filter.eventually_gt_atTop (1 : ℝ)] with X hs hX
  have hx : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos hX
  have hp : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hl _
  have hs' : Real.log X ^ (1 + 5 * B) ≤ 1 / 2 * X ^ d := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hl _),
      abs_of_pos (Real.rpow_pos_of_pos hx _)] using hs
  have heq : Real.log X * (Real.log X ^ B) ^ (5 : ℕ) =
      Real.log X ^ (1 + 5 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le, Real.rpow_add hl]
    simp only [Real.rpow_one]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm B (5 : ℝ)]
  have hpow : Real.sqrt X * X ^ d = windowY X ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    congr 1
    dsimp [d]; ring
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hp 5)).mpr
  calc
    2 * Real.sqrt X * Real.log X * (Real.log X ^ B) ^ (5 : ℕ) =
        2 * Real.sqrt X * Real.log X ^ (1 + 5 * B) := by rw [← heq]; ring
    _ ≤ 2 * Real.sqrt X * (1 / 2 * X ^ d) :=
      mul_le_mul_of_nonneg_left hs' (by positivity)
    _ = windowY X ε := by rw [← hpow]; ring

/-- Derived elementary estimate for P0088 page 15, the passage to the reciprocal logarithm prime model. -/
theorem psc_tail_global_bound (X Y u v : ℝ) (hX : 1 ≤ X) (hXY : 0 < X - Y) :
    ∑ m ∈ (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
      (if m.Prime then 0 else (ArithmeticFunction.vonMangoldt m : ℝ)) ≤
      2 * Real.sqrt X * Real.log X := by
  classical
  calc
    _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊,
        (if m.Prime then 0 else (ArithmeticFunction.vonMangoldt m : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        have hm' := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
        have hm0 : 0 < m := by
          by_contra hn
          have : m = 0 := by omega
          subst m
          simp only [Nat.cast_zero] at hm'
          linarith [hm'.1]
        exact Finset.mem_Ioc.mpr ⟨hm0, Nat.le_floor hm'.2.le⟩
      · intro m _ _
        split_ifs <;> positivity
    _ = Chebyshev.psi X - Chebyshev.theta X := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _
      split_ifs <;> simp_all
    _ ≤ _ := Chebyshev.psi_sub_theta_le hX

/-- Derived elementary estimate for P0088 page 15, the passage to the reciprocal logarithm prime model. -/
theorem psc_window_log_absorb (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∀ᶠ X : ℝ in Filter.atTop,
      1 ≤ windowY X ε ∧ 2 * windowY X ε ≤ X ∧
      4 * windowY X ε ^ 2 / X ≤
        windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  let d : ℝ := 1 - (7 / 12 + ε / 2)
  have hd : 0 < d := by dsimp [d]; linarith
  have ht := (isLittleO_log_rpow_rpow_atTop (5 * B) hd).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [ht, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (1 : ℝ)] with X hs hl1 hX
  have hx : 0 < X := by linarith
  have hl : 0 < Real.log X := by linarith
  have hp : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hl _
  have hp1 : 1 ≤ (Real.log X ^ B) ^ (5 : ℕ) := by
    exact one_le_pow₀ (Real.one_le_rpow hl1 hB.le)
  have hy : 0 < windowY X ε := Real.rpow_pos_of_pos hx _
  have hy1 : 1 ≤ windowY X ε := Real.one_le_rpow hX.le (by linarith)
  have hs' : Real.log X ^ (5 * B) ≤ 1 / 4 * X ^ d := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hl _),
      abs_of_pos (Real.rpow_pos_of_pos hx _)] using hs
  have hpow : windowY X ε * X ^ d = X := by
    rw [windowY, ← Real.rpow_add hx,
      show 7 / 12 + ε / 2 + d = 1 by dsimp [d]; ring, Real.rpow_one]
  have hp5 : (Real.log X ^ B) ^ (5 : ℕ) = Real.log X ^ (5 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm B (5 : ℝ)]
  have hYP : windowY X ε * (Real.log X ^ B) ^ (5 : ℕ) ≤ X / 4 := by
    rw [hp5]
    calc
      _ ≤ windowY X ε * (1 / 4 * X ^ d) := mul_le_mul_of_nonneg_left hs' hy.le
      _ = (windowY X ε * X ^ d) / 4 := by ring
      _ = X / 4 := by rw [hpow]
  have hYle : windowY X ε ≤ X / 4 :=
    (le_mul_of_one_le_right hy.le hp1).trans hYP
  refine ⟨hy1, by linarith, ?_⟩
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hp 5)).mpr
  rw [div_mul_eq_mul_div, div_le_iff₀ hx]
  nlinarith [mul_le_mul_of_nonneg_left hYP hy.le]

/-- Derived elementary estimate for P0088 page 15, the passage to the reciprocal logarithm prime model. -/
theorem psc_log_swap_bound (S : Finset ℕ) (X Y : ℝ) (hX : 0 < X)
    (hL : 1 ≤ Real.log X) (hY : 0 ≤ Y) (hYX : 2 * Y ≤ X)
    (hS : ∀ m ∈ S, X - Y ≤ (m : ℝ) ∧ (m : ℝ) ≤ X)
    (hc : (S.card : ℝ) ≤ 2 * Y) (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) :
    ‖(∑ m ∈ S, if m.Prime then a m else 0) -
      (∑ m ∈ S, if m.Prime then a m * (Real.log (m : ℝ) : ℂ) else 0) /
        (Real.log X : ℂ)‖ ≤ 4 * Y ^ 2 / X := by
  have hL0 : 0 < Real.log X := by linarith
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ S, (2 * Y / X) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hm1, hm2⟩ := hS m hm
      have hgap : 0 ≤ Real.log X - Real.log (m : ℝ) ∧
          Real.log X - Real.log (m : ℝ) ≤ 2 * Y / X := by
        have hm0 : 0 < (m : ℝ) := by linarith
        refine ⟨sub_nonneg.mpr (Real.log_le_log hm0 hm2), ?_⟩
        have hg := Real.log_le_sub_one_of_pos (div_pos hX hm0)
        rw [Real.log_div hX.ne' hm0.ne'] at hg
        apply hg.trans
        apply (le_div_iff₀ hX).mpr
        calc
          (X / (m : ℝ) - 1) * X = (X - (m : ℝ)) * X / (m : ℝ) := by field_simp
          _ ≤ Y * X / (m : ℝ) := by gcongr; linarith
          _ ≤ 2 * Y := (div_le_iff₀ hm0).mpr (by nlinarith)
      obtain ⟨hg0, hg⟩ := hgap
      have hr : ‖(1 : ℂ) - (Real.log (m : ℝ) : ℂ) / (Real.log X : ℂ)‖ ≤
          2 * Y / X := by
        rw [← Complex.ofReal_div, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        have he : 1 - Real.log (m : ℝ) / Real.log X =
            (Real.log X - Real.log (m : ℝ)) / Real.log X := by field_simp
        rw [he, abs_of_nonneg (div_nonneg hg0 hL0.le)]
        exact (div_le_self hg0 hL).trans hg
      by_cases hp : m.Prime
      · simp only [if_pos hp]
        rw [show a m - a m * (Real.log (m : ℝ) : ℂ) / (Real.log X : ℂ) =
          a m * (1 - (Real.log (m : ℝ) : ℂ) / (Real.log X : ℂ)) by ring, norm_mul]
        exact (mul_le_mul_of_nonneg_right (ha m) (norm_nonneg _)).trans (by simpa using hr)
      · simp only [if_neg hp, zero_div, sub_self, norm_zero]
        positivity
    _ = (S.card : ℝ) * (2 * Y / X) := by simp
    _ ≤ (2 * Y) * (2 * Y / X) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * Y ^ 2 / X := by ring

/-- Derived elementary estimate for P0088 page 15, the passage to the reciprocal logarithm prime model. -/
theorem psc_reciprocal_swap_bound (S : Finset ℕ) (X Y : ℝ) (hX : 0 < X)
    (hL : 1 ≤ Real.log X) (hY : 0 ≤ Y) (hYX : 2 * Y ≤ X)
    (hS : ∀ m ∈ S, X - Y ≤ (m : ℝ) ∧ (m : ℝ) ≤ X ∧ 1 ≤ Real.log (m : ℝ))
    (hc : (S.card : ℝ) ≤ 2 * Y) :
    |(S.card : ℝ) / Real.log X - ∑ m ∈ S, 1 / Real.log (m : ℝ)| ≤
      4 * Y ^ 2 / X := by
  have hL0 : 0 < Real.log X := by linarith
  have he : (S.card : ℝ) / Real.log X = ∑ _m ∈ S, 1 / Real.log X := by simp [div_eq_mul_inv]
  rw [he, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ S, |1 / Real.log X - 1 / Real.log (m : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ S, 2 * Y / X := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨hm1, hm2, hmL⟩ := hS m hm
      have hmL0 : 0 < Real.log (m : ℝ) := by linarith
      have hgap : 0 ≤ Real.log X - Real.log (m : ℝ) ∧
          Real.log X - Real.log (m : ℝ) ≤ 2 * Y / X := by
        have hm0 : 0 < (m : ℝ) := by linarith
        refine ⟨sub_nonneg.mpr (Real.log_le_log hm0 hm2), ?_⟩
        have hg := Real.log_le_sub_one_of_pos (div_pos hX hm0)
        rw [Real.log_div hX.ne' hm0.ne'] at hg
        apply hg.trans
        apply (le_div_iff₀ hX).mpr
        calc
          (X / (m : ℝ) - 1) * X = (X - (m : ℝ)) * X / (m : ℝ) := by field_simp
          _ ≤ Y * X / (m : ℝ) := by gcongr; linarith
          _ ≤ 2 * Y := (div_le_iff₀ hm0).mpr (by nlinarith)
      obtain ⟨hg0, hg⟩ := hgap
      have heq : 1 / Real.log X - 1 / Real.log (m : ℝ) =
          -(Real.log X - Real.log (m : ℝ)) / (Real.log X * Real.log (m : ℝ)) := by
        field_simp; ring
      rw [heq, abs_div, abs_neg, abs_of_nonneg hg0,
        abs_of_pos (mul_pos hL0 hmL0)]
      exact (div_le_self hg0 (by nlinarith : 1 ≤ Real.log X * Real.log (m : ℝ))).trans hg
    _ = (S.card : ℝ) * (2 * Y / X) := by simp
    _ ≤ (2 * Y) * (2 * Y / X) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * Y ^ 2 / X := by ring

/-- LEAF: P0088 page 15, Section 4 first paragraph, the short interval form of
the Siegel Walfisz theorem, von Mangoldt weighted, for hypothesis A1.2 of page 5
with a nonprincipal character of modulus at most `log X ^ B`.
Class HARD. -/
theorem psc_leaf_siegel_walfisz_short (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
            ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * χ m‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  sorry

/-- LEAF: P0088 page 15, Section 4 first paragraph, Huxley's theorem on primes
in short intervals, von Mangoldt weighted: on every subinterval of the window
`I1` of length `X ^ (7/12 + ε/2)` the von Mangoldt sum equals the number of
integers up to a saving of any power of `log X`.
Class HARD. -/
theorem psc_leaf_huxley_short (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ u v : ℝ, X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        |∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
            ((ArithmeticFunction.vonMangoldt m : ℝ) - 1)| ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  sorry

/-! ### Elementary helpers for the three MEDIUM leaves, AI written -/

/-- Elementary: for `δ > 0`, any constant times any power of `log X` is eventually
below `X ^ δ`. -/
theorem psc_eventually_logpow_le (δ A c : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X in Filter.atTop, c * Real.log X ^ A ≤ X ^ δ := by
  have h := (isLittleO_log_rpow_rpow_atTop A hδ).bound
    (show (0:ℝ) < 1 / (|c| + 1) by positivity)
  filter_upwards [h, Filter.eventually_ge_atTop (1:ℝ)] with X hX hX1
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hX
  have h0 : c * Real.log X ^ A ≤ (|c| + 1) * Real.log X ^ A :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) (Real.rpow_nonneg hL _)
  calc _ ≤ (|c| + 1) * Real.log X ^ A := h0
    _ ≤ (|c| + 1) * (1 / (|c| + 1) * X ^ δ) := by gcongr
    _ = X ^ δ := by field_simp

/-- Elementary: the size facts on the window `I1` used by the three MEDIUM leaves,
with `windowY X ε = X ^ (7/12 + ε/2)` and `7/12 + ε/2 ≤ 53/72 < 1`. -/
theorem psc_window_facts (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 11 / 36) :
    ∃ X0 : ℝ, 6 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      1 ≤ windowY X ε ∧ 4 * windowY X ε ≤ X ∧ 1 ≤ Real.log X ∧
      4 * windowY X ε / X ≤ (Real.log X ^ B) ^ (-5 : ℤ) ∧
      6 * Real.sqrt X * Real.log X ^ 2 ≤ windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  set θ := 7 / 12 + ε / 2 with hθ
  have h1 := psc_eventually_logpow_le (1 - θ) (5 * B) 4 (by rw [hθ]; linarith)
  have h2 := psc_eventually_logpow_le (θ - 1 / 2) (5 * B + 2) 6 (by rw [hθ]; linarith)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 (h1.and h2)
  refine ⟨max 6 X1, le_max_left _ _, fun X hX => ?_⟩
  have hX6 : 6 ≤ X := le_trans (le_max_left _ _) hX
  obtain ⟨e1, e2⟩ := hX1 X (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact (Real.exp_one_lt_d9.trans (show (2.7182818286 : ℝ) < 6 by norm_num)).le.trans hX6
  have hL0 : 0 < Real.log X := by linarith
  have hY : windowY X ε = X ^ θ := rfl
  rw [hY]
  set L := Real.log X with hLdef
  have hE : (L ^ B) ^ (-5 : ℤ) = 1 / L ^ (5 * B) := by
    rw [show (-5 : ℤ) = -((5 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul hL0.le, one_div]
    norm_num [mul_comm]
  rw [hE]
  have hP1 : 1 ≤ L ^ (5 * B) := Real.one_le_rpow hL (by positivity)
  have hPpos : 0 < L ^ (5 * B) := by linarith
  have hXs : X ^ (1 - θ) * X ^ θ = X := by rw [← Real.rpow_add hX0]; simp
  have hsq : Real.sqrt X * X ^ (θ - 1 / 2) = X ^ θ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]; ring_nf
  have hYpos : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 _
  have hY1 : 1 ≤ X ^ θ := Real.one_le_rpow (by linarith) (by rw [hθ]; linarith)
  have hθpos : 0 < X ^ (1 - θ) := Real.rpow_pos_of_pos hX0 _
  have k1 : 4 * X ^ θ * L ^ (5 * B) ≤ X := by
    calc 4 * X ^ θ * L ^ (5 * B) = (4 * L ^ (5 * B)) * X ^ θ := by ring
      _ ≤ X ^ (1 - θ) * X ^ θ := by gcongr
      _ = X := hXs
  have hL2 : L ^ (2 : ℕ) * L ^ (5 * B) = L ^ (5 * B + 2) := by
    rw [Real.rpow_add hL0, ← Real.rpow_natCast]; push_cast; ring
  refine ⟨hY1, ?_, hL, ?_, ?_⟩
  · nlinarith
  · rw [div_le_div_iff₀ hX0 hPpos]; linarith
  · rw [mul_one_div, le_div_iff₀ hPpos]
    have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    calc 6 * Real.sqrt X * L ^ 2 * L ^ (5 * B)
        = Real.sqrt X * (6 * (L ^ (2 : ℕ) * L ^ (5 * B))) := by ring
      _ = Real.sqrt X * (6 * L ^ (5 * B + 2)) := by rw [hL2]
      _ ≤ Real.sqrt X * X ^ (θ - 1 / 2) := by gcongr
      _ = X ^ θ := hsq

/-- Elementary: the window `[X - Y, X)` holds at most `Y + 1` integers. -/
theorem psc_card_window_le (X Y : ℝ) (hY : 0 ≤ Y) (S : Finset ℕ)
    (hS : ∀ m ∈ S, X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X) : (S.card : ℝ) ≤ Y + 1 := by
  have hsub : S ⊆ Finset.Ico ⌈X - Y⌉₊ ⌈X⌉₊ := by
    intro m hm
    obtain ⟨h1, h2⟩ := hS m hm
    rw [Finset.mem_Ico]
    exact ⟨Nat.ceil_le.2 h1, Nat.lt_ceil.2 h2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hc' : (S.card : ℝ) ≤ ((⌈X⌉₊ - ⌈X - Y⌉₊ : ℕ) : ℝ) := by exact_mod_cast hc
  by_cases hle : ⌈X - Y⌉₊ ≤ ⌈X⌉₊
  · rw [Nat.cast_sub hle] at hc'
    by_cases hX : 0 ≤ X
    · have a1 : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one hX
      have a2 : X - Y ≤ (⌈X - Y⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    · have : ⌈X⌉₊ = 0 := Nat.ceil_eq_zero.2 (by linarith)
      rw [this] at hc'
      have : (0 : ℝ) ≤ (⌈X - Y⌉₊ : ℝ) := Nat.cast_nonneg _
      simp at hc'
      linarith
  · have h0 : S.card = 0 := by omega
    rw [h0, Nat.cast_zero]
    linarith

/-- Elementary: on the window, `0 ≤ log X - log m ≤ 2 Y / X` once `4 Y ≤ X`. -/
theorem psc_log_gap {X Y : ℝ} {m : ℕ} (hX : 0 < X) (hY4 : 4 * Y ≤ X)
    (h1 : X - Y ≤ (m : ℝ)) (h2 : (m : ℝ) < X) :
    0 ≤ Real.log X - Real.log m ∧ Real.log X - Real.log m ≤ 2 * Y / X := by
  have hm : 0 < (m : ℝ) := by linarith
  have hY0 : 0 ≤ Y := by linarith
  refine ⟨by linarith [Real.log_le_log hm h2.le], ?_⟩
  rw [← Real.log_div hX.ne' hm.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hX hm)
  have h3 : X / m - 1 = (X - m) / m := by field_simp
  have h4 : (X - m) / m ≤ 2 * Y / X := by
    rw [div_le_div_iff₀ hm hX]; nlinarith
  linarith

/-- LEAF: P0088 page 15, Section 4 first paragraph, the passage from the von
Mangoldt weight to the primes: the prime powers `p ^ k` with `k ≥ 2` in the
window carry von Mangoldt mass at most `sqrt X * log X ^ 2`, which is below
`windowY X ε` over any power of `log X` since `7/12 > 1/2`.
Class MEDIUM. -/
theorem psc_leaf_prime_power_tail (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ u v : ℝ, X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
            (if m.Prime then 0 else (ArithmeticFunction.vonMangoldt m : ℝ)) ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  obtain ⟨X0, hX0, hF⟩ := psc_window_facts B ε hB hε hε1
  refine ⟨1, X0, one_pos, by linarith, fun X hX u v hu huv hv => ?_⟩
  obtain ⟨hY1, hY4, hL, -, hT⟩ := hF X hX
  have hXp : 0 < X := by linarith
  set Y := windowY X ε
  set S := (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v)
  have hmem : ∀ m ∈ S, X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X := by
    intro m hm
    simp only [S, primeWindow, Finset.mem_filter] at hm
    exact hm.1.2
  set T := S.filter (fun m => ¬ m.Prime ∧ IsPrimePow m)
  have hterm : ∀ m ∈ S, (if m.Prime then 0 else (ArithmeticFunction.vonMangoldt m : ℝ)) ≤
      (if (¬ m.Prime ∧ IsPrimePow m) then Real.log X else 0) := by
    intro m hm
    obtain ⟨h1, h2⟩ := hmem m hm
    by_cases hp : m.Prime
    · simp [hp]
    · by_cases hq : IsPrimePow m
      · rw [if_neg hp, if_pos ⟨hp, hq⟩]
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        have hm : 0 < (m : ℝ) := by linarith
        exact Real.log_le_log hm h2.le
      · rw [if_neg hp, if_neg (fun h => hq h.2)]
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hq]
  have hsum : ∑ m ∈ S, (if m.Prime then 0 else (ArithmeticFunction.vonMangoldt m : ℝ)) ≤
      (T.card : ℝ) * Real.log X := by
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- injection of `T` into pairs `(p, k)` with `p ≤ sqrt X` and `k ≤ 2 log X`
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hmaps : ∀ m ∈ T, (m.minFac, m.factorization m.minFac) ∈
      Finset.range (⌊Real.sqrt X⌋₊ + 1) ×ˢ Finset.range (⌊2 * Real.log X⌋₊ + 1) := by
    intro m hm
    simp only [T, Finset.mem_filter] at hm
    obtain ⟨hmS, hp, hq⟩ := hm
    obtain ⟨h1, h2⟩ := hmem m hmS
    have heq := hq.minFac_pow_factorization_eq
    set p := m.minFac
    set k := m.factorization p
    have hpp : p.Prime := Nat.minFac_prime hq.ne_one
    have hk2 : 2 ≤ k := by
      by_contra hk
      interval_cases k
      · simp at heq; exact hq.ne_one heq.symm
      · rw [pow_one] at heq; exact hp (heq ▸ hpp)
    have hmX : (m : ℝ) ≤ X := h2.le
    have hmR : ((p : ℝ)) ^ k = (m : ℝ) := by exact_mod_cast heq
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    constructor
    · apply Nat.lt_succ_of_le
      apply Nat.le_floor
      rw [Real.le_sqrt (by positivity) hXp.le]
      calc (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ hp1 hk2
        _ = m := hmR
        _ ≤ X := hmX
    · apply Nat.lt_succ_of_le
      apply Nat.le_floor
      have h2k : (2 : ℝ) ^ k ≤ X := by
        calc (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := by
              gcongr; exact_mod_cast hpp.two_le
          _ = m := hmR
          _ ≤ X := hmX
      have := Real.log_le_log (by positivity) h2k
      rw [Real.log_pow] at this
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith
  have hinj : Set.InjOn (fun m : ℕ => (m.minFac, m.factorization m.minFac)) T := by
    intro m hm n hn hmn
    simp only [T, Finset.coe_filter, Set.mem_ofPred_eq] at hm hn
    simp only [Prod.mk.injEq] at hmn
    calc m = m.minFac ^ m.factorization m.minFac := hm.2.2.minFac_pow_factorization_eq.symm
      _ = n.minFac ^ n.factorization n.minFac := by rw [hmn.2, hmn.1]
      _ = n := hn.2.2.minFac_pow_factorization_eq
  have hcardT := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at hcardT
  have hcR : (T.card : ℝ) ≤ (Real.sqrt X + 1) * (2 * Real.log X + 1) := by
    have : (T.card : ℝ) ≤ ((⌊Real.sqrt X⌋₊ : ℝ) + 1) * ((⌊2 * Real.log X⌋₊ : ℝ) + 1) := by
      exact_mod_cast hcardT
    refine this.trans ?_
    gcongr
    · exact Nat.floor_le (Real.sqrt_nonneg _)
    · exact Nat.floor_le (by linarith)
  have hs1 : 1 ≤ Real.sqrt X := by
    rw [Real.le_sqrt zero_le_one hXp.le]; linarith
  calc _ ≤ (T.card : ℝ) * Real.log X := hsum
    _ ≤ (Real.sqrt X + 1) * (2 * Real.log X + 1) * Real.log X := by gcongr
    _ ≤ (2 * Real.sqrt X) * (3 * Real.log X) * Real.log X := by gcongr <;> linarith
    _ = 6 * Real.sqrt X * Real.log X ^ 2 := by ring
    _ ≤ Y * (Real.log X ^ B) ^ (-5 : ℤ) := hT
    _ = _ := by ring

/-- LEAF: P0088 page 15, Section 4 first paragraph, the partial summation step
from `log p` weights to unit weights on the primes of the window: since every
`m` in `I1` has `log X - log m ≤ log X - log (X - windowY X ε)`, swapping
`1 / log p` for `1 / log X` costs at most about `windowY X ε ^ 2 / X`, uniformly
in a weight of modulus at most one.
Class MEDIUM. -/
theorem psc_leaf_log_weight_swap (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ a : ℕ → ℂ, (∀ m, ‖a m‖ ≤ 1) →
      ∀ u v : ℝ, X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖(∑ m ∈ (primeWindow X (windowY X ε)).filter
              (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
              (if m.Prime then a m else 0)) -
          (∑ m ∈ (primeWindow X (windowY X ε)).filter
              (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
              (if m.Prime then a m * ((Real.log (m : ℝ) : ℝ) : ℂ) else 0)) /
            ((Real.log X : ℝ) : ℂ)‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  obtain ⟨X0, hX0, hF⟩ := psc_window_facts B ε hB hε hε1
  refine ⟨1, X0, one_pos, by linarith, fun X hX a ha u v hu huv hv => ?_⟩
  obtain ⟨hY1, hY4, hL, hE, -⟩ := hF X hX
  have hXp : 0 < X := by linarith
  set Y := windowY X ε
  set S := (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v)
  have hmem : ∀ m ∈ S, X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X := by
    intro m hm
    simp only [S, primeWindow, Finset.mem_filter] at hm
    exact hm.1.2
  have hcard := psc_card_window_le X Y (by linarith) S hmem
  have hLc : ((Real.log X : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.log X ≠ 0 by linarith)
  have hid : (∑ m ∈ S, (if m.Prime then a m else 0)) -
      (∑ m ∈ S, (if m.Prime then a m * ((Real.log (m : ℝ) : ℝ) : ℂ) else 0)) /
        ((Real.log X : ℝ) : ℂ) =
      ∑ m ∈ S, (if m.Prime then a m *
        (((Real.log X - Real.log m) / Real.log X : ℝ) : ℂ) else 0) := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hp : m.Prime
    · simp only [if_pos hp]
      push_cast
      field_simp
    · simp [hp]
  rw [hid]
  have hterm : ∀ m ∈ S, ‖(if m.Prime then a m *
      (((Real.log X - Real.log m) / Real.log X : ℝ) : ℂ) else 0)‖ ≤ 2 * Y / X := by
    intro m hm
    obtain ⟨h1, h2⟩ := hmem m hm
    obtain ⟨g1, g2⟩ := psc_log_gap hXp hY4 h1 h2
    have hYX : 0 ≤ 2 * Y / X := by positivity
    by_cases hp : m.Prime
    · rw [if_pos hp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg g1 (by linarith))]
      calc ‖a m‖ * ((Real.log X - Real.log m) / Real.log X)
          ≤ 1 * ((Real.log X - Real.log m) / Real.log X) := by
            gcongr; exact ha m
        _ ≤ Real.log X - Real.log m := by rw [one_mul]; exact div_le_self g1 hL
        _ ≤ 2 * Y / X := g2
    · simp [hp, hYX]
  calc _ ≤ ∑ m ∈ S, ‖(if m.Prime then a m *
          (((Real.log X - Real.log m) / Real.log X : ℝ) : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, 2 * Y / X := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (2 * Y / X) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y + 1) * (2 * Y / X) := by gcongr
    _ ≤ Y * (4 * Y / X) := by
        rw [show Y * (4 * Y / X) = (2 * Y) * (2 * Y / X) by ring]
        gcongr; linarith
    _ ≤ Y * (Real.log X ^ B) ^ (-5 : ℤ) := by gcongr
    _ = _ := by ring

/-- LEAF: P0088 page 15, f1 u = 1 / log u, the same swap on all integers of
the subinterval: the sum of `1 / log m` over the integers of `[u, v)` inside
`I1` is their number over `log X` up to about `windowY X ε ^ 2 / X`.
Class MEDIUM. -/
theorem psc_leaf_reciprocal_log_count (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ u v : ℝ, X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        |(((primeWindow X (windowY X ε)).filter
              (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v)).card : ℝ) / Real.log X -
          ∑ m ∈ (primeWindow X (windowY X ε)).filter
              (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v), 1 / Real.log (m : ℝ)| ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  obtain ⟨X0, hX0, hF⟩ := psc_window_facts B ε hB hε hε1
  refine ⟨1, X0, one_pos, by linarith, fun X hX u v hu huv hv => ?_⟩
  obtain ⟨hY1, hY4, hL, hE, -⟩ := hF X hX
  have hXp : 0 < X := by linarith
  set Y := windowY X ε
  set S := (primeWindow X Y).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v)
  have hmem : ∀ m ∈ S, X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X := by
    intro m hm
    simp only [S, primeWindow, Finset.mem_filter] at hm
    exact hm.1.2
  have hcard := psc_card_window_le X Y (by linarith) S hmem
  have hterm : ∀ m ∈ S, |1 / Real.log X - 1 / Real.log (m : ℝ)| ≤ 2 * Y / X := by
    intro m hm
    obtain ⟨h1, h2⟩ := hmem m hm
    obtain ⟨g1, g2⟩ := psc_log_gap hXp hY4 h1 h2
    have hm3 : 3 ≤ (m : ℝ) := by linarith
    have hlm : 1 ≤ Real.log (m : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact (Real.exp_one_lt_d9.trans (show (2.7182818286 : ℝ) < 3 by norm_num)).le.trans hm3
    have hid : 1 / Real.log (m : ℝ) - 1 / Real.log X =
        (Real.log X - Real.log m) / (Real.log m * Real.log X) := by
      field_simp
    rw [abs_sub_comm, hid, abs_of_nonneg (div_nonneg g1 (by positivity))]
    exact (div_le_self g1 (one_le_mul_of_one_le_of_one_le hlm hL)).trans g2
  have hsum : (S.card : ℝ) / Real.log X - ∑ m ∈ S, 1 / Real.log (m : ℝ) =
      ∑ m ∈ S, (1 / Real.log X - 1 / Real.log (m : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  rw [hsum]
  have hYX : 0 ≤ 2 * Y / X := by positivity
  calc _ ≤ ∑ m ∈ S, |1 / Real.log X - 1 / Real.log (m : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ S, 2 * Y / X := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (2 * Y / X) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Y + 1) * (2 * Y / X) := by gcongr
    _ ≤ Y * (4 * Y / X) := by
        rw [show Y * (4 * Y / X) = (2 * Y) * (2 * Y / X) by ring]
        gcongr; linarith
    _ ≤ Y * (Real.log X ^ B) ^ (-5 : ℤ) := by gcongr
    _ = _ := by ring

/-! ### Assembly -/

/-- Elementary: `Λ m * a m` splits into its prime part and its prime power part. -/
theorem psc_vonMangoldt_split (S : Finset ℕ) (a : ℕ → ℂ) :
    ∑ m ∈ S, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * a m =
      ∑ m ∈ S, (if m.Prime then a m * ((Real.log (m : ℝ) : ℝ) : ℂ) else 0) +
      ∑ m ∈ S, (if m.Prime then 0 else ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * a m) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hp : m.Prime
  · rw [if_pos hp, if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    ring
  · rw [if_neg hp, if_neg hp, zero_add]

/-- Elementary: the prime power part has norm at most its von Mangoldt mass. -/
theorem psc_tail_norm_le (S : Finset ℕ) (a : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ 1) :
    ‖∑ m ∈ S, (if m.Prime then 0 else ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * a m)‖ ≤
      ∑ m ∈ S, (if m.Prime then 0 else (ArithmeticFunction.vonMangoldt m : ℝ)) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  by_cases hp : m.Prime
  · simp [hp]
  · rw [if_neg hp, if_neg hp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (ha m)

/-- Elementary: `log X ≥ 1` once `X ≥ 3`. -/
theorem psc_one_le_log {X : ℝ} (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact (Real.exp_one_lt_d9.trans (by norm_num)).le.trans hX

/-- `leaf_nonprincipal_prime_character_sum` of
`SPLIT_prime_short_interval_character.lean`, exact statement, from the leaves
`psc_leaf_siegel_walfisz_short`, `psc_leaf_prime_power_tail` and
`psc_leaf_log_weight_swap`. Fully proved from the leaves. -/
theorem leaf_nonprincipal_prime_character_sum_from_leaves (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
            (if m.Prime then χ m else 0)‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  obtain ⟨C1, X1, hC1, hX1, h1⟩ := psc_leaf_siegel_walfisz_short B ε hB hε hε1
  obtain ⟨C2, X2, hC2, hX2, h2⟩ := psc_leaf_prime_power_tail B ε hB hε hε1
  obtain ⟨C3, X3, hC3, hX3, h3⟩ := psc_leaf_log_weight_swap B ε hB hε hε1
  refine ⟨C1 + C2 + C3, max 3 (max X1 (max X2 X3)), by positivity,
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro X hX q hq hqB χ hχ u v hu huv hv
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_max_left _ _) hX
  have hXr : max X1 (max X2 X3) ≤ X := le_trans (le_max_right _ _) hX
  have hX1' : X1 ≤ X := le_trans (le_max_left _ _) hXr
  have hX2' : X2 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hXr
  have hX3' : X3 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hXr
  have hL : 1 ≤ Real.log X := psc_one_le_log hX3
  set S := (primeWindow X (windowY X ε)).filter
    (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v) with hS
  set a : ℕ → ℂ := fun m => χ m with ha_def
  have ha : ∀ m, ‖a m‖ ≤ 1 := fun m => DirichletCharacter.norm_le_one χ _
  set R := windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) with hR
  have hRnn : 0 ≤ R := by
    have hX0 : 0 < X := by linarith
    have hL0 : 0 < Real.log X := by linarith
    exact mul_nonneg (Real.rpow_pos_of_pos hX0 _).le
      (zpow_pos (Real.rpow_pos_of_pos hL0 B) _).le
  have e1 := h1 X hX1' q hq hqB χ hχ u v hu huv hv
  have e2 := h2 X hX2' u v hu huv hv
  have e3 := h3 X hX3' a ha u v hu huv hv
  set P := ∑ m ∈ S, (if m.Prime then a m else 0)
  set Q := ∑ m ∈ S, (if m.Prime then a m * ((Real.log (m : ℝ) : ℝ) : ℂ) else 0)
  set N := ∑ m ∈ S, (if m.Prime then 0 else ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * a m)
  set V := ∑ m ∈ S, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * a m
  have hsplit : V = Q + N := psc_vonMangoldt_split S a
  have hN : ‖N‖ ≤ C2 * R := by
    rw [hR, ← mul_assoc]; exact (psc_tail_norm_le S a ha).trans e2
  have hV : ‖V‖ ≤ C1 * R := by rw [hR, ← mul_assoc]; exact e1
  have hPQ : ‖P - Q / ((Real.log X : ℝ) : ℂ)‖ ≤ C3 * R := by
    rw [hR, ← mul_assoc]; exact e3
  have hLc : ((Real.log X : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.log X ≠ 0 by linarith)
  have hid : P = (P - Q / ((Real.log X : ℝ) : ℂ)) + (V - N) / ((Real.log X : ℝ) : ℂ) := by
    rw [hsplit]; field_simp; ring
  have hdiv : ‖(V - N) / ((Real.log X : ℝ) : ℂ)‖ ≤ ‖V - N‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact div_le_self (norm_nonneg _) hL
  have hfin : ‖P‖ ≤ (C1 + C2 + C3) * R := by
    rw [hid]
    calc _ ≤ ‖P - Q / ((Real.log X : ℝ) : ℂ)‖ + ‖(V - N) / ((Real.log X : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ C3 * R + (‖V‖ + ‖N‖) := by
          gcongr
          exact hdiv.trans (norm_sub_le _ _)
      _ ≤ C3 * R + (C1 * R + C2 * R) := by gcongr
      _ = (C1 + C2 + C3) * R := by ring
  calc _ = ‖P‖ := rfl
    _ ≤ (C1 + C2 + C3) * R := hfin
    _ = _ := by rw [hR]; ring

/-- `leaf_principal_prime_count_level_one` of
`SPLIT_prime_short_interval_character.lean`, exact statement, from the leaves
`psc_leaf_huxley_short`, `psc_leaf_prime_power_tail`, `psc_leaf_log_weight_swap`
and `psc_leaf_reciprocal_log_count`. Fully proved from the leaves. -/
theorem leaf_principal_prime_count_level_one_from_leaves (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ u v : ℝ,
        X - windowY X ε ≤ u → u ≤ v → v ≤ X →
        ‖∑ m ∈ (primeWindow X (windowY X ε)).filter
            (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v),
            ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ))‖ ≤
          C * windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) := by
  obtain ⟨C1, X1, hC1, hX1, h1⟩ := psc_leaf_huxley_short B ε hB hε hε1
  obtain ⟨C2, X2, hC2, hX2, h2⟩ := psc_leaf_prime_power_tail B ε hB hε hε1
  obtain ⟨C3, X3, hC3, hX3, h3⟩ := psc_leaf_log_weight_swap B ε hB hε hε1
  obtain ⟨C4, X4, hC4, hX4, h4⟩ := psc_leaf_reciprocal_log_count B ε hB hε hε1
  refine ⟨C1 + C2 + C3 + C4, max 3 (max X1 (max X2 (max X3 X4))), by positivity,
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro X hX u v hu huv hv
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_max_left _ _) hX
  have hXr : max X1 (max X2 (max X3 X4)) ≤ X := le_trans (le_max_right _ _) hX
  have hXr2 : max X2 (max X3 X4) ≤ X := le_trans (le_max_right _ _) hXr
  have hXr3 : max X3 X4 ≤ X := le_trans (le_max_right _ _) hXr2
  have hX1' : X1 ≤ X := le_trans (le_max_left _ _) hXr
  have hX2' : X2 ≤ X := le_trans (le_max_left _ _) hXr2
  have hX3' : X3 ≤ X := le_trans (le_max_left _ _) hXr3
  have hX4' : X4 ≤ X := le_trans (le_max_right _ _) hXr3
  have hL : 1 ≤ Real.log X := psc_one_le_log hX3
  set S := (primeWindow X (windowY X ε)).filter
    (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) < v) with hS
  set a : ℕ → ℂ := fun _ => 1 with ha_def
  have ha : ∀ m, ‖a m‖ ≤ 1 := fun m => by simp [ha_def]
  set R := windowY X ε * (Real.log X ^ B) ^ (-5 : ℤ) with hR
  have e1 := h1 X hX1' u v hu huv hv
  have e2 := h2 X hX2' u v hu huv hv
  have e3 := h3 X hX3' a ha u v hu huv hv
  have e4 := h4 X hX4' u v hu huv hv
  set P := ∑ m ∈ S, (if m.Prime then a m else 0)
  set Q := ∑ m ∈ S, (if m.Prime then a m * ((Real.log (m : ℝ) : ℝ) : ℂ) else 0)
  set N := ∑ m ∈ S, (if m.Prime then 0 else ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * a m)
  set V := ∑ m ∈ S, ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * a m
  set W := ∑ m ∈ S, ((1 / Real.log (m : ℝ) : ℝ) : ℂ)
  set K : ℂ := ((S.card : ℝ) : ℂ)
  have hsplit : V = Q + N := psc_vonMangoldt_split S a
  have hN : ‖N‖ ≤ C2 * R := by
    rw [hR, ← mul_assoc]; exact (psc_tail_norm_le S a ha).trans e2
  have hVK : ‖V - K‖ ≤ C1 * R := by
    rw [hR, ← mul_assoc]
    have : V - K = ((∑ m ∈ S, ((ArithmeticFunction.vonMangoldt m : ℝ) - 1) : ℝ) : ℂ) := by
      simp only [V, K, ha_def, mul_one]
      push_cast
      rw [Finset.sum_sub_distrib]
      simp
    rw [this, Complex.norm_real, Real.norm_eq_abs]; exact e1
  have hPQ : ‖P - Q / ((Real.log X : ℝ) : ℂ)‖ ≤ C3 * R := by
    rw [hR, ← mul_assoc]; exact e3
  have hKW : ‖K / ((Real.log X : ℝ) : ℂ) - W‖ ≤ C4 * R := by
    rw [hR, ← mul_assoc]
    have : K / ((Real.log X : ℝ) : ℂ) - W =
        (((S.card : ℝ) / Real.log X - ∑ m ∈ S, 1 / Real.log (m : ℝ) : ℝ) : ℂ) := by
      simp only [K, W]
      push_cast
      rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]; exact e4
  have hLc : ((Real.log X : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.log X ≠ 0 by linarith)
  have hsum : ∑ m ∈ S, ((if m.Prime then (1 : ℂ) else 0) - ((1 / Real.log (m : ℝ) : ℝ) : ℂ)) =
      P - W := by
    rw [Finset.sum_sub_distrib]
  have hid : P - W = (P - Q / ((Real.log X : ℝ) : ℂ)) +
      ((V - K) - N) / ((Real.log X : ℝ) : ℂ) + (K / ((Real.log X : ℝ) : ℂ) - W) := by
    rw [hsplit]; field_simp; ring
  have hdiv : ‖((V - K) - N) / ((Real.log X : ℝ) : ℂ)‖ ≤ ‖(V - K) - N‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact div_le_self (norm_nonneg _) hL
  have hfin : ‖P - W‖ ≤ (C1 + C2 + C3 + C4) * R := by
    rw [hid]
    calc _ ≤ ‖(P - Q / ((Real.log X : ℝ) : ℂ)) + ((V - K) - N) / ((Real.log X : ℝ) : ℂ)‖ +
            ‖K / ((Real.log X : ℝ) : ℂ) - W‖ := norm_add_le _ _
      _ ≤ (‖P - Q / ((Real.log X : ℝ) : ℂ)‖ + ‖((V - K) - N) / ((Real.log X : ℝ) : ℂ)‖) +
            ‖K / ((Real.log X : ℝ) : ℂ) - W‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (C3 * R + (‖V - K‖ + ‖N‖)) + C4 * R := by
          gcongr
          exact hdiv.trans (norm_sub_le _ _)
      _ ≤ (C3 * R + (C1 * R + C2 * R)) + C4 * R := by gcongr
      _ = (C1 + C2 + C3 + C4) * R := by ring
  rw [hsum]
  calc _ ≤ (C1 + C2 + C3 + C4) * R := hfin
    _ = _ := by rw [hR]; ring

#print axioms leaf_nonprincipal_prime_character_sum_from_leaves
#print axioms leaf_principal_prime_count_level_one_from_leaves

/-- P0088 page 15, the smooth reciprocal logarithm model on the open interval above one. -/
theorem psc_reciprocal_log_smooth : ContDiffOn ℝ ⊤ (fun u : ℝ => 1 / Real.log u) (Set.Ioi 1) := by
  refine contDiffOn_const.div (Real.contDiffOn_log.mono ?_) ?_
  · intro u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    change 1 < u at hu
    linarith
  · intro u hu
    exact (Real.log_pos hu).ne'

/-- Derived obstruction for the endpoint PNT route to P0088 page 15. -/
theorem psc_long_interval_majorant_not_short (a c : ℝ) (ha : a < 1) :
    ¬ ∃ C X0 : ℝ, ∀ X : ℝ, max 2 X0 ≤ X →
      X * Real.exp (-c * Real.sqrt (Real.log X)) ≤ C * X ^ a := by
  rintro ⟨C, X0, hC⟩
  have hCp : 0 < C := by
    have hz : 0 < max (2 : ℝ) X0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have h := hC (max 2 X0) le_rfl
    have hp : 0 < max (2 : ℝ) X0 ^ a := Real.rpow_pos_of_pos hz _
    have hl : 0 < max (2 : ℝ) X0 * Real.exp (-c * Real.sqrt (Real.log (max 2 X0))) := by positivity
    by_contra hnot
    have hnon : C ≤ 0 := le_of_not_gt hnot
    have hn := mul_nonpos_of_nonpos_of_nonneg hnon hp.le
    linarith
  let u : ℝ := max (max 2 X0) ((|c| + |Real.log C| + 2) / (1 - a))
  have hu : 2 ≤ u := (le_max_left 2 X0).trans (le_max_left _ _)
  have huX0 : max 2 X0 ≤ u := le_max_left _ _
  have hub : (|c| + |Real.log C| + 2) / (1 - a) ≤ u := le_max_right _ _
  have hd : 0 < 1 - a := by linarith
  have hm := (div_le_iff₀ hd).mp hub
  have hq : |Real.log C| + 2 ≤ (1 - a) * u - c := by linarith [le_abs_self c]
  have hprod : 2 * (|Real.log C| + 2) ≤ u * ((1 - a) * u - c) :=
    mul_le_mul hu hq (by positivity) (by linarith)
  have hgap : Real.log C + u ^ 2 * a < u ^ 2 - c * u := by
    nlinarith [le_abs_self (Real.log C), abs_nonneg (Real.log C)]
  have hX : max 2 X0 ≤ Real.exp (u ^ 2) := by
    have hh := Real.add_one_le_exp (u ^ 2)
    nlinarith [sq_nonneg (u - 1)]
  have h := hC (Real.exp (u ^ 2)) hX
  rw [Real.log_exp, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ u)] at h
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
  have hl : Real.exp (u ^ 2) * Real.exp (-c * u) = Real.exp (u ^ 2 - c * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hr : C * Real.exp (u ^ 2 * a) = Real.exp (Real.log C + u ^ 2 * a) := by
    rw [Real.exp_add, Real.exp_log hCp]
  rw [hl, hr] at h
  exact (not_lt_of_ge h) (Real.exp_lt_exp.mpr hgap)

end LeanLab.KumchevLiu2007.Task556a
