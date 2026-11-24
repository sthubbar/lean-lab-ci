/-
PROVED leaf `leaf_trunc_coeff_bound` of SPLIT_Decomp409b, P0069 page 27 line 4: the coefficients
of M1 N L satisfy (3.1) with B' = 2|B| + 3. Restated verbatim as `leaf_trunc_coeff_bound_proof`.
Route: pairs m, n with mn | k number at most tau k squared, each weight at most tau k ^ |B|, and the
truncated Moebius sum at most tau l, l | k. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_Decomp409b

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409b
open Finset Decomp1518
attribute [local instance] Classical.propDecidable


theorem tau_eq_card (n : ℕ) : tau n = (n.divisors.card : ℝ) := by
  simp [tau, ArithmeticFunction.sigma_zero_apply]

theorem tau_mono {m k : ℕ} (h : m ∣ k) (hk : k ≠ 0) : tau m ≤ tau k := by
  rw [tau_eq_card, tau_eq_card]; exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hk h)

theorem one_le_tau {k : ℕ} (hk : k ≠ 0) : 1 ≤ tau k := by
  rw [tau_eq_card]; exact_mod_cast Finset.card_pos.2 ⟨1, by simp [hk]⟩

theorem pow_le_abs {t B : ℝ} (ht : 1 ≤ t) : t ^ B ≤ t ^ |B| :=
  Real.rpow_le_rpow_of_exponent_le ht (le_abs_self B)

theorem psiTrunc_norm_le {l : ℕ} (hl : l ≠ 0) (w γ : ℝ) : ‖psiTrunc l w γ‖ ≤ tau l := by
  unfold psiTrunc
  refine (norm_sum_le _ _).trans ?_
  rw [tau_eq_card]
  calc _ ≤ ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ (d : ℝ) < γ, (1 : ℝ) := by
        refine sum_le_sum fun d _ => ?_
        have := @ArithmeticFunction.abs_moebius_le_one d
        rw [show ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ = |((ArithmeticFunction.moebius d : ℤ) : ℝ)| by
          rw [← Complex.norm_intCast]]
        exact_mod_cast this
    _ ≤ _ := by
        rw [sum_const, nsmul_one]
        exact_mod_cast Finset.card_le_card fun d hd => by
          simp only [mem_filter] at hd; simp [hd.2.1, hl]

/-- Generic bound: a double sum over m ~ M, n ~ N with `mn ∣ k`, each term bounded by
`tau k ^ (2|B|+1)`, is at most `tau k ^ (2|B|+3)`. -/
theorem dsum_le {k : ℕ} (hk : k ≠ 0) (M N : ℝ) (B : ℝ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ m n, m * n ∣ k → f m n ≤ tau k ^ (2 * |B| + 1)) :
    (∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      if m * n ∣ k then f m n else 0) ≤ tau k ^ (2 * |B| + 3) := by
  set T := tau k
  have hT : 1 ≤ T := one_le_tau hk
  have hT0 : 0 ≤ T ^ (2 * |B| + 1) := Real.rpow_nonneg (by linarith) _
  have step : ∀ m, (∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊, if m * n ∣ k then f m n else 0) ≤
      if m ∣ k then T * T ^ (2 * |B| + 1) else 0 := by
    intro m
    split_ifs with hm
    · calc _ ≤ ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊, if n ∈ k.divisors then T ^ (2 * |B| + 1) else 0 := by
            refine sum_le_sum fun n _ => ?_
            split_ifs with h1 h2
            · exact hf m n h1
            · exact absurd (Nat.mem_divisors.2 ⟨Dvd.dvd.trans (Dvd.intro_left _ rfl) h1, hk⟩) h2
            · exact hT0
            · exact le_rfl
        _ = ∑ n ∈ (Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter (· ∈ k.divisors), T ^ (2 * |B| + 1) := by
            rw [sum_filter]
        _ ≤ T * T ^ (2 * |B| + 1) := by
            rw [sum_const, nsmul_eq_mul, show T = _ from tau_eq_card k]
            refine mul_le_mul_of_nonneg_right ?_ (by rw [← show T = _ from tau_eq_card k]; exact hT0)
            exact_mod_cast Finset.card_le_card (fun x hx => (mem_filter.1 hx).2)
    · refine (sum_eq_zero fun n _ => ?_).le
      exact ite_eq_right_iff.2 fun h' => absurd h' fun h => hm (Dvd.dvd.trans (Dvd.intro _ rfl) h)
  have hT1 : 0 ≤ T * T ^ (2 * |B| + 1) := mul_nonneg (by linarith) hT0
  calc _ ≤ ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, if m ∈ k.divisors then T * T ^ (2 * |B| + 1) else 0 := by
          refine sum_le_sum fun m _ => (step m).trans ?_
          split_ifs with h1 h2
          · exact le_rfl
          · exact absurd (Nat.mem_divisors.2 ⟨h1, hk⟩) h2
          · exact hT1
          · exact le_rfl
    _ = ∑ m ∈ (Ioc ⌊M⌋₊ ⌊2 * M⌋₊).filter (· ∈ k.divisors), T * T ^ (2 * |B| + 1) := by
          rw [sum_filter]
    _ ≤ T * (T * T ^ (2 * |B| + 1)) := by
          rw [sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hT1
          rw [show T = _ from tau_eq_card k]
          exact_mod_cast Finset.card_le_card (fun x hx => (mem_filter.1 hx).2)
    _ = T ^ (2 * |B| + 3) := by
          have hT0' : 0 < T := by linarith
          rw [show 2 * |B| + 3 = 1 + (1 + (2 * |B| + 1)) by ring, Real.rpow_add hT0' 1,
            Real.rpow_add hT0' 1, Real.rpow_one]

theorem coef_le {a : ℕ → ℂ} {B : ℝ} (ha : ∀ k, ‖a k‖ ≤ tau k ^ B) {m k : ℕ} (hm : m ∣ k)
    (hk : k ≠ 0) : ‖a m‖ ≤ tau k ^ |B| := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hk (zero_dvd_iff.1 hm)
  calc ‖a m‖ ≤ tau m ^ B := ha m
    _ ≤ tau m ^ |B| := pow_le_abs (one_le_tau hm0)
    _ ≤ tau k ^ |B| := Real.rpow_le_rpow (by linarith [one_le_tau hm0]) (tau_mono hm hk) (abs_nonneg _)

theorem triple_le {T x y z B : ℝ} (hT : 1 ≤ T) (_hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hx : x ≤ T ^ |B|) (hy : y ≤ T ^ |B|) (hz : z ≤ T) : x * y * z ≤ T ^ (2 * |B| + 1) := by
  have hT0 : 0 < T := by linarith
  rw [show 2 * |B| + 1 = |B| + |B| + 1 by ring, Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_one]
  have := Real.rpow_nonneg hT0.le |B|
  exact mul_le_mul (mul_le_mul hx hy hy0 this) hz hz0 (mul_nonneg this this)

/-- `leaf_trunc_coeff_bound`, verbatim, proved. -/
theorem leaf_trunc_coeff_bound_proof (B : ℝ) : ∃ B' : ℝ, ∀ (a b : ℕ → ℂ) (M N w γ : ℝ),
    (∀ k, ‖a k‖ ≤ tau k ^ B) → (∀ k, ‖b k‖ ≤ tau k ^ B) →
    ∀ k : ℕ, ‖(if k = 0 then 0 else conv2T a b M N w γ k)‖ ≤ tau k ^ B' := by
  refine ⟨2 * |B| + 3, fun a b M N w γ ha hb k => ?_⟩
  by_cases hk : k = 0
  · subst hk
    simp only [ite_true, norm_zero]
    rw [tau_eq_card]; simp only [Nat.divisors_zero, card_empty, Nat.cast_zero]
    rw [Real.zero_rpow (by positivity)]
  rw [if_neg hk]
  unfold conv2T
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (sum_le_sum fun m _ => norm_sum_le _ _) ?_
  have e : ∀ m n, ‖(if m * n ∣ k then a m * b n * psiTrunc (k / (m * n)) w γ else 0)‖ =
      if m * n ∣ k then ‖a m * b n * psiTrunc (k / (m * n)) w γ‖ else 0 := by
    intro m n; split_ifs <;> simp
  simp only [e]
  refine dsum_le hk M N B _ fun m n hmn => ?_
  have hl : k / (m * n) ≠ 0 := by
    intro h; rcases hmn with ⟨c, hc⟩
    have hmn0 : m * n ≠ 0 := by rintro h0; rw [h0, zero_mul] at hc; exact hk hc
    rw [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hmn0)] at h
    exact hk (by rw [hc, h, mul_zero])
  rw [norm_mul, norm_mul]
  exact triple_le (one_le_tau hk) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (coef_le ha (Dvd.dvd.trans (Dvd.intro _ rfl) hmn) hk)
    (coef_le hb (Dvd.dvd.trans (Dvd.intro_left _ rfl) hmn) hk)
    ((psiTrunc_norm_le hl w γ).trans (tau_mono (Nat.div_dvd_of_dvd hmn) hk))


#print axioms leaf_trunc_coeff_bound_proof

end LeanLab.BakerHarmanPintz1997.Decomp409b
