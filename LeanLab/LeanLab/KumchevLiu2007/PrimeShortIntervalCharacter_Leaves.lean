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

namespace LeanLab.KumchevLiu2007.Task556a

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators
attribute [local instance] Classical.propDecidable

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
  sorry

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
  sorry

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
  sorry

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

end LeanLab.KumchevLiu2007.Task556a
