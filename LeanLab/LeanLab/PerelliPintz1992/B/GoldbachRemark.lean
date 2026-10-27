-- Repo encoding of P0070 from cloud runs, copied under namespace B by PC run 20261020T0603Z-352, unit U-1182, unchanged otherwise.
/-
P0070 Perelli-Pintz 1992, the Goldbach remark of page 356, read from the page image of
papers/P0070.pdf. Unit U-5076, CLOUD 20261019T0213Z-cloud14.

STATED as cited: `GoldbachRemark`, for `I = [x, x + x^{1/2+ε}]`, all even `2n ∈ I` but
`O(|I| L^{-B})` satisfy `r(2n) = 2n 𝔖(2n) + O(x log^{-A} x)`, `r(2n) = Σ_{2n = h + k} Λ(h)Λ(k)`.
PROVED: `r_le_of_not_goldbach`, an `m ≥ 2` that is not a sum of two primes has
`r(m) ≤ 2 log m (ψ(m) - θ(m))`, every pair holding a prime power that is not prime;
`r_le_sqrt`, so `r(m) ≤ 4 √m log² m`; and `exceptions_of_remark`, the remark gives
`#{even m ∈ I not a sum of two primes} ≤ C |I| L^{-B}`, the link to the lab's exceptional set counts.
This is far weaker than Baker-Harman-Pintz 1997, P0069, whose exponent is 11/160, and than
Montgomery-Vaughan; it is the paper's own remark. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.PerelliPintz1992.B.SingPos

namespace LeanLab.PerelliPintz1992.B
open Finset Real Chebyshev
open scoped ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `r(m) = Σ_{h + k = m} Λ(h) Λ(k)`. -/
def r (m : ℕ) : ℝ := ∑ h ∈ range (m + 1), Λ h * Λ (m - h)

/-- The remark of page 356, CITED: for `0 < ε < 1/2` and `A, B > 0`, for large `x`, all even
`m ∈ [x, x + x^{1/2+ε}]` but at most `C₂ x^{1/2+ε} log^{-B} x` satisfy
`|r(m) - m 𝔖(m)| ≤ C₁ x log^{-A} x`, with the paper's `𝔖(2n)` our `Sing n`. -/
def GoldbachRemark : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ A B : ℝ, 0 < A → 0 < B → ∃ C₁ C₂ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    (((Icc ⌈x⌉₊ ⌊x + x ^ (1 / 2 + ε)⌋₊).filter (fun m => Even m ∧
        C₁ * x * Real.log x ^ (-A) < |r m - m * Sing (m / 2)|)).card : ℝ) ≤
      C₂ * x ^ (1 / 2 + ε) * Real.log x ^ (-B)

/-- The non-prime part of `Λ`. -/
def f (k : ℕ) : ℝ := if k.Prime then 0 else Λ k

lemma sum_f (m : ℕ) : ∑ k ∈ range (m + 1), f k = ψ m - θ m := by
  rw [psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter, range_eq_Ico]
  have : Ico 0 (m + 1) = insert 0 (Ioc 0 m) := by
    ext k; simp only [mem_Ico, mem_insert, mem_Ioc]; omega
  rw [this, sum_insert (by simp)]
  simp only [f, Nat.not_prime_zero, if_false, ArithmeticFunction.map_zero, zero_add]
  exact sum_congr rfl fun k _ => by split_ifs <;> rfl

/-- A number `m ≥ 2` that is not a sum of two primes has `r(m) ≤ 2 log m (ψ(m) - θ(m))`. -/
theorem r_le_of_not_goldbach {m : ℕ} (hm : 2 ≤ m) (hg : ¬ IsGoldbachSum m) :
    r m ≤ 2 * Real.log m * (ψ m - θ m) := by
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hΛle : ∀ k, k ≤ m → Λ k ≤ Real.log m := fun k hk => by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [hlog0]
    · exact le_trans ArithmeticFunction.vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hk))
  have hterm : ∀ h ∈ range (m + 1),
      Λ h * Λ (m - h) ≤ Real.log m * f h + Real.log m * f (m - h) := by
    intro h hh
    have hhm : h ≤ m := by simp at hh; omega
    have hA := ArithmeticFunction.vonMangoldt_nonneg (n := h)
    have hB := ArithmeticFunction.vonMangoldt_nonneg (n := m - h)
    have hf0 : ∀ k, 0 ≤ f k := fun k => by unfold f; split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
    by_cases ph : h.Prime
    · by_cases pk : (m - h).Prime
      · exact absurd ⟨h, m - h, ph, pk, by omega⟩ hg
      · have : f (m - h) = Λ (m - h) := by simp [f, pk]
        rw [this]
        have := mul_le_mul_of_nonneg_right (hΛle h hhm) hB
        nlinarith [mul_nonneg hlog0 (hf0 h)]
    · have : f h = Λ h := by simp [f, ph]
      rw [this]
      have := mul_le_mul_of_nonneg_left (hΛle (m - h) (by omega)) hA
      nlinarith [mul_nonneg hlog0 (hf0 (m - h))]
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hrefl : ∑ h ∈ range (m + 1), f (m - h) = ∑ h ∈ range (m + 1), f h := by
    rw [← sum_range_reflect]
    exact sum_congr rfl fun h hh => by simp at hh; congr 1; omega
  rw [hrefl, sum_f] at hsum
  unfold r
  linarith

/-- With Mathlib's `|ψ - θ| ≤ 2 √x log x`: `r(m) ≤ 4 √m log² m` for non-Goldbach `m ≥ 2`. -/
theorem r_le_sqrt {m : ℕ} (hm : 2 ≤ m) (hg : ¬ IsGoldbachSum m) :
    r m ≤ 4 * Real.sqrt m * Real.log m ^ 2 := by
  have h1 := r_le_of_not_goldbach hm hg
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have h2 := abs_psi_sub_theta_le_sqrt_mul_log (x := (m : ℝ)) (by exact_mod_cast (by omega : 1 ≤ m))
  have h3 : ψ m - θ m ≤ 2 * Real.sqrt m * Real.log m := le_trans (le_abs_self _) h2
  nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * Real.log m)]

/-- Eventually `4 √(2x) log²(2x) + C₁ x / log x < 2 twinC x`. -/
lemma eventually_main (C₁ : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      4 * Real.sqrt (2 * x) * Real.log (2 * x) ^ 2 + C₁ * x * Real.log x ^ (-(1 : ℝ)) <
        2 * ChenExplicit.twinC * x := by
  have ht := ChenExplicit.twinC_pos
  set c := 2 * ChenExplicit.twinC with hc
  have hc0 : 0 < c := by positivity
  -- log y ≤ y^{1/8} eventually
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log (2 * x) ≤ (2 * x) ^ (1 / 8 : ℝ) := by
    have := (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually
      (hlo.and (Filter.eventually_ge_atTop 1))
    filter_upwards [this] with x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [id] at h1 h2
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h2),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at h1
    exact h1
  -- the two small terms
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, (C₁ + 1) / Real.log x < c / 2 := by
    have := Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop (2 * (C₁ + 1) / c + 1))
    filter_upwards [this, Filter.eventually_gt_atTop (Real.exp 1)] with x hx hx1
    have hl : 1 < Real.log x := by
      rw [Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos 1])]; exact hx1
    rw [div_lt_iff₀ (by linarith)]
    have : 2 * (C₁ + 1) / c < Real.log x := by linarith
    rw [div_lt_iff₀ hc0] at this
    rcases le_or_gt (C₁ + 1) 0 with h | h
    · nlinarith
    · nlinarith
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, 4 * (2 * x) ^ (3 / 4 : ℝ) < c / 2 * x := by
    have h2 : 0 < (2 : ℝ) ^ (3 / 4 : ℝ) := by positivity
    have := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually
      (Filter.eventually_gt_atTop (8 * 2 ^ (3 / 4 : ℝ) / c))
    filter_upwards [this, Filter.eventually_gt_atTop 0] with x hx hx0
    rw [Real.mul_rpow (by norm_num) hx0.le]
    have hx34 : x = x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    have h34 : 0 < x ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
    rw [div_lt_iff₀ hc0] at hx
    conv_rhs => rw [hx34]
    nlinarith [mul_lt_mul_of_pos_left hx h34]
  filter_upwards [e1, e2, e3, Filter.eventually_gt_atTop (Real.exp 1)] with x h1 h2 h3 hx
  have hx0 : 0 < x := by linarith [Real.exp_pos 1]
  have hx1 : 1 < x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hl : 1 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt hx0]; exact hx
  have hl2 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  -- √(2x) log²(2x) ≤ (2x)^{1/2} (2x)^{1/4} = (2x)^{3/4}
  have hs : Real.sqrt (2 * x) = (2 * x) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsq : Real.log (2 * x) ^ 2 ≤ ((2 * x) ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hl2 h1 2
  have hpow : ((2 * x) ^ (1 / 8 : ℝ)) ^ 2 = (2 * x) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hmul : (2 * x) ^ (1 / 2 : ℝ) * (2 * x) ^ (1 / 4 : ℝ) = (2 * x) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hA : 4 * Real.sqrt (2 * x) * Real.log (2 * x) ^ 2 ≤ 4 * (2 * x) ^ (3 / 4 : ℝ) := by
    rw [hs, ← hmul, ← hpow]
    have : 0 ≤ (2 * x) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_left hsq this]
  have hB : C₁ * x * Real.log x ^ (-(1 : ℝ)) ≤ (C₁ + 1) / Real.log x * x := by
    rw [Real.rpow_neg_one]
    have hlx : 0 < Real.log x := by linarith
    rw [show C₁ * x * (Real.log x)⁻¹ = C₁ / Real.log x * x by field_simp]
    have : C₁ / Real.log x ≤ (C₁ + 1) / Real.log x := div_le_div_of_nonneg_right (by linarith) hlx.le
    nlinarith
  have := mul_lt_mul_of_pos_right h2 hx0
  linarith

/-- The remark bounds the Goldbach exceptions in `[x, x + x^{1/2+ε}]`. -/
theorem exceptions_of_remark (hR : GoldbachRemark) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    {B : ℝ} (hB : 0 < B) : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (((Icc ⌈x⌉₊ ⌊x + x ^ (1 / 2 + ε)⌋₊).filter (fun m => Even m ∧ ¬ IsGoldbachSum m)).card
        : ℝ) ≤ C * x ^ (1 / 2 + ε) * Real.log x ^ (-B) := by
  obtain ⟨C₁, C₂, x₀, hC⟩ := hR ε hε hε1 1 B one_pos hB
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp (eventually_main C₁)
  refine ⟨C₂, max (max x₀ x₁) 4, fun x hx => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  refine le_trans ?_ (hC x hx0)
  rw [Nat.cast_le]
  apply card_le_card
  intro m hm
  simp only [mem_filter, mem_Icc] at hm ⊢
  obtain ⟨⟨hm1, hm2⟩, hev, hng⟩ := hm
  refine ⟨⟨hm1, hm2⟩, hev, ?_⟩
  have hxm : x ≤ m := le_trans (Nat.le_ceil x) (by exact_mod_cast hm1)
  have hpow : x ^ (1 / 2 + ε) ≤ x := by
    calc x ^ (1 / 2 + ε) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x := Real.rpow_one x
  have hm2x : (m : ℝ) ≤ 2 * x := by
    have := Nat.floor_le (show 0 ≤ x + x ^ (1 / 2 + ε) by positivity)
    have : (m : ℝ) ≤ x + x ^ (1 / 2 + ε) := le_trans (by exact_mod_cast hm2) this
    linarith
  have hm2 : 2 ≤ m := by
    have : (4 : ℝ) ≤ m := le_trans hx4 hxm
    exact_mod_cast (by linarith : (2 : ℝ) ≤ m)
  have hr := r_le_sqrt hm2 hng
  have hS := sing_ge (m / 2)
  have ht := ChenExplicit.twinC_pos
  have hmain : 2 * ChenExplicit.twinC * x ≤ m * Sing (m / 2) := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hS hm0]
  have hsq : Real.sqrt m * Real.log m ^ 2 ≤ Real.sqrt (2 * x) * Real.log (2 * x) ^ 2 := by
    have h1 : Real.sqrt m ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt hm2x
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have h2 : Real.log m ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hm2x
    have h3 : Real.log m ^ 2 ≤ Real.log (2 * x) ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg hm1') h2 2
    exact mul_le_mul h1 h3 (sq_nonneg _) (Real.sqrt_nonneg _)
  have hev' := hx₁ x hx1
  rw [lt_abs]
  right
  linarith

end

end LeanLab.PerelliPintz1992.B

