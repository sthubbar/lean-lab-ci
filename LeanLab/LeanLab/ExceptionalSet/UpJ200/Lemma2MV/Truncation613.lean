/-
P0015 Montgomery and Vaughan 1975, display (6.13) on page 363, the truncation of the
singular series weight: with `P = ⌊X^{6δ}⌋`, `(X/P) Σ_{q ≤ P} q |g_n(q)| ≪ X^{1+δ}/P`,
here in the form with the Heath-Brown weight `gm n q` and `X / X^{6δ}` in place of `X/P`.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.HeathBrown1985.SingularSeries
import LeanLab.HeathBrown1985.DivisorEps

noncomputable section
namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MV

open Real Finset Filter

/-- Partial summation identity used for P0015 display 6.13 on page 363: the weight q is
written as the number of F below q, so the q weighted sum becomes a sum of tails. -/
theorem trunc613_abel (g : ℕ → ℝ) (P : ℕ) :
    ∑ q ∈ Ioc 0 P, (q : ℝ) * g q = ∑ F ∈ range P, ∑ q ∈ Ioc F P, g q := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le P), sum_range_succ, ih]
    have h1 : ∑ F ∈ range P, ∑ q ∈ Ioc F (P + 1), g q =
        ∑ F ∈ range P, (∑ q ∈ Ioc F P, g q + g (P + 1)) := by
      apply sum_congr rfl
      intro F hF
      rw [Finset.sum_Ioc_succ_top (le_of_lt (mem_range.mp hF))]
    rw [h1, sum_add_distrib, sum_const, card_range, Nat.Ioc_succ_singleton, sum_singleton]
    push_cast
    simp only [nsmul_eq_mul]
    ring

/-- The q weighted sum of the singular series terms, P0015 display 6.13 on page 363:
the sum over q up to P of q times the absolute value of g at q is at most
48 times the square of one plus log P times the square of the divisor count of n. -/
theorem trunc613_weighted_sum_le (n P : ℕ) (hn : 1 ≤ n) (hP : 1 ≤ P) :
    ∑ q ∈ Icc 1 P, |LeanLab.HeathBrown1985.gm n q| * (q : ℝ) ≤
      48 * (1 + Real.log P) ^ 2 * (n.divisors.card : ℝ) ^ 2 := by
  set g := fun q => |LeanLab.HeathBrown1985.gm n q| with hg
  set d : ℝ := (n.divisors.card : ℝ) with hd
  have hd1 : 1 ≤ d := by
    have : 0 < n.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    rw [hd]; exact_mod_cast this
  have hL0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP)
  set K : ℝ := (6 + 2 * Real.log P) * d ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hIcc : Icc 1 P = Ioc 0 P := by ext x; simp; omega
  have hrw : ∑ q ∈ Icc 1 P, |LeanLab.HeathBrown1985.gm n q| * (q : ℝ) =
      ∑ q ∈ Ioc 0 P, (q : ℝ) * g q := by
    rw [hIcc]; apply sum_congr rfl; intro q _; simp [hg, mul_comm]
  rw [hrw, trunc613_abel]
  have hterm : ∀ F ∈ range P, ∑ q ∈ Ioc F P, g q ≤ 8 * K / ((F : ℝ) + 1) := by
    intro F hF
    rcases Nat.eq_zero_or_pos F with h0 | hpos
    · subst h0
      rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hP]
      have h01 : ∑ q ∈ Ioc 0 1, g q = 1 := by
        simp [hg, LeanLab.HeathBrown1985.gm_one]
      have h1P := LeanLab.HeathBrown1985.sum_abs_gm_Ioc_le n 1 P hn le_rfl
      simp only [Nat.cast_one, Real.log_one] at h1P
      rw [h01]
      have : (1 : ℝ) + 4 * ((6 + 2 * 0) * d ^ 2 / 1) ≤ 8 * K / ((0 : ℕ) + 1 : ℝ) := by
        rw [hK]; push_cast; nlinarith
      linarith
    · have hFP := LeanLab.HeathBrown1985.sum_abs_gm_Ioc_le n F P hn hpos
      have hF1 : (1 : ℝ) ≤ F := by exact_mod_cast hpos
      have hFle : (F : ℝ) ≤ P := by exact_mod_cast le_of_lt (mem_range.mp hF)
      have hlog : Real.log F ≤ Real.log P := Real.log_le_log (by linarith) hFle
      have hnum : (6 + 2 * Real.log F) * d ^ 2 ≤ K := by
        rw [hK]; apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      have : 4 * ((6 + 2 * Real.log F) * d ^ 2 / F) ≤ 8 * K / ((F : ℝ) + 1) := by
        have h2 : 4 * ((6 + 2 * Real.log F) * d ^ 2 / F) ≤ 4 * (K / F) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact div_le_div_of_nonneg_right hnum (by linarith)
        have h3 : 4 * (K / F) ≤ 8 * K / ((F : ℝ) + 1) := by
          rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith
        linarith
      exact le_trans hFP this
  have hharm : ∑ F ∈ range P, (1 : ℝ) / ((F : ℝ) + 1) ≤ 1 + Real.log P := by
    have h := harmonic_le_one_add_log P
    have : ((harmonic P : ℚ) : ℝ) = ∑ F ∈ range P, (1 : ℝ) / ((F : ℝ) + 1) := by
      simp [harmonic]
    linarith
  calc ∑ F ∈ range P, ∑ q ∈ Ioc F P, g q
      ≤ ∑ F ∈ range P, 8 * K / ((F : ℝ) + 1) := sum_le_sum hterm
    _ = 8 * K * ∑ F ∈ range P, (1 : ℝ) / ((F : ℝ) + 1) := by
        rw [mul_sum]; apply sum_congr rfl; intro F _; ring
    _ ≤ 8 * K * (1 + Real.log P) := mul_le_mul_of_nonneg_left hharm (by positivity)
    _ ≤ 48 * (1 + Real.log P) ^ 2 * d ^ 2 := by
        rw [hK]; nlinarith [sq_nonneg d, mul_nonneg hL0 (sq_nonneg d)]

/-- P0015 display 6.13 on page 363, in the Heath-Brown gm form: the truncated q weighted
singular series sum with `P = ⌊X^{6δ}⌋` is at most a constant times `X^{1+δ}/X^{6δ}`. -/
theorem trunc613_main : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (X / X ^ (6 * δ)) * ∑ q ∈ Finset.Icc 1 ⌊X ^ (6 * δ)⌋₊,
          |LeanLab.HeathBrown1985.gm n q| * q ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  refine ⟨1, one_pos, fun δ hδ hδ1 => ?_⟩
  set k : ℕ := ⌈4 / δ⌉₊ with hkdef
  have hk4 : 4 / δ ≤ (k : ℝ) := Nat.le_ceil _
  have hk : 1 ≤ k := by
    have : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk4
    exact_mod_cast this
  have hkinv : (k : ℝ)⁻¹ ≤ δ / 4 := by
    have := inv_anti₀ (by positivity : (0 : ℝ) < 4 / δ) hk4
    rwa [inv_div] at this
  obtain ⟨Cd, hCd, hdiv⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  set ε : ℝ := 1 / (14 * Cd) with hε
  have hεpos : 0 < ε := by positivity
  have hlo := (isLittleO_log_rpow_atTop (r := δ / 4) (by positivity)).bound hεpos
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hlo
  refine ⟨max X1 (Real.exp 1), fun X hX n hn hnX => ?_⟩
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXone : 1 ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hXe
  have hXpos : 0 < X := by linarith
  have hlogX1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]; exact hXe
  set Y : ℝ := X ^ (δ / 4) with hY
  have hYpos : 0 < Y := by positivity
  have hlog : Real.log X ≤ ε * Y := by
    have h := hX1 X (le_trans (le_max_left _ _) hX)
    rwa [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hYpos.le] at h
  set P : ℕ := ⌊X ^ (6 * δ)⌋₊ with hPdef
  have hP1 : 1 ≤ P := by
    apply Nat.le_floor; simp only [Nat.cast_one]
    exact Real.one_le_rpow hXone (by positivity)
  have hPX : (P : ℝ) ≤ X := by
    calc (P : ℝ) ≤ X ^ (6 * δ) := Nat.floor_le (by positivity)
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hXone (by linarith)
      _ = X := Real.rpow_one X
  have hlogP : Real.log P ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hP1) hPX
  have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast hP1)
  have hA : 1 + Real.log P ≤ 2 * ε * Y := by linarith
  have hd : (n.divisors.card : ℝ) ≤ Cd * Y := by
    calc (n.divisors.card : ℝ) ≤ Cd * (n : ℝ) ^ ((k : ℝ)⁻¹) := hdiv n hn
      _ ≤ Cd * X ^ ((k : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hCd.le
          exact Real.rpow_le_rpow (by positivity) hnX (by positivity)
      _ ≤ Cd * Y := by
          apply mul_le_mul_of_nonneg_left _ hCd.le
          exact Real.rpow_le_rpow_of_exponent_le hXone hkinv
  have hS := trunc613_weighted_sum_le n P hn hP1
  have hY4 : Y ^ (4 : ℕ) = X ^ δ := by
    rw [hY, ← Real.rpow_mul_natCast hXpos.le]; congr 1; push_cast; ring
  have hεC : ε * Cd = 1 / 14 := by rw [hε]; field_simp
  have hS2 : ∑ q ∈ Icc 1 P, |LeanLab.HeathBrown1985.gm n q| * (q : ℝ) ≤ X ^ δ := by
    have h1 : (1 + Real.log P) ^ 2 ≤ (2 * ε * Y) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hA 2
    have h2 : (n.divisors.card : ℝ) ^ 2 ≤ (Cd * Y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hd 2
    have h3 : 48 * (1 + Real.log P) ^ 2 * (n.divisors.card : ℝ) ^ 2 ≤
        48 * (2 * ε * Y) ^ 2 * (Cd * Y) ^ 2 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity)
        (by positivity)
    have h4 : 48 * (2 * ε * Y) ^ 2 * (Cd * Y) ^ 2 = 192 * (ε * Cd) ^ 2 * Y ^ (4 : ℕ) := by
      ring
    rw [h4, hεC, hY4] at h3
    have hXd : 0 ≤ X ^ δ := by positivity
    nlinarith
  calc (X / X ^ (6 * δ)) * ∑ q ∈ Finset.Icc 1 P, |LeanLab.HeathBrown1985.gm n q| * (q : ℝ)
      ≤ (X / X ^ (6 * δ)) * X ^ δ := mul_le_mul_of_nonneg_left hS2 (by positivity)
    _ = 1 * (X ^ (1 + δ) / X ^ (6 * δ)) := by
        rw [Real.rpow_add hXpos, Real.rpow_one]; ring

end LeanLab.ExceptionalSet.UpJ200.Lemma2MV

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MV.trunc613_main
