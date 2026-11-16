/-
P0069 Baker Harman Pintz 1997, pages 6 and 7, displays 2.4 and 2.5.
Display 2.5 at a fixed x with the arcs of page 5: with T = (log x)^D, the arcs have
denominators at most T² and half widths T⁴/(qY). Under three size conditions on T, Y
and the Farey order Q, the major arc integral differs from the principal model of
display 2.6 by an explicit multiple of the prefix sum bounds of hypotheses i and iv.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Route512MajorUnion

namespace LeanLab.BHP1997.Route512Major
open Classical Complex MeasureTheory Set

/-- P0069 page 7 display 2.5 at a fixed `x`: with `T = (log x)^D`, arcs of denominators
at most `T²` and half widths `T⁴/(qY)` inside the period `(1/Q, 1 + 1/Q]`, the major arc
integral of S1 S2 e(-Nt) differs from the principal model of display 2.6 by at most
`40 T¹² M₁ V / Y + 120 ‖w₁‖ T¹⁶ M₂`, where `M₁`, `M₂` bound the prefix sums of
hypotheses i and iv and `V` bounds the sum of `‖b‖`. -/
theorem major_fixed512j (T Y : ℝ) (hT : 1 ≤ T) (hY : 0 < Y) (Q : ℕ)
    (loI hiI loJ hiJ : ℕ) (a b : ℕ → ℂ) (w₁ w₂ : ℂ) (M₁ M₂ V T₁ T₂ : ℝ) (N : ℕ)
    (hT₁ : (hiI : ℝ) ≤ T₁) (hT₂ : (hiJ : ℝ) ≤ T₂)
    (hnI : ((hiI - loI : ℕ) : ℝ) ≤ 3 * Y) (hnJ : ((hiJ - loJ : ℕ) : ℝ) ≤ 3 * Y)
    (hc1 : 2 * T ^ 2 ≤ (Q : ℝ)) (hc2 : 2 * T ^ 8 < Y) (hc3 : T ^ 4 * (Q : ℝ) ≤ Y)
    (hsupp : ∀ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, ∀ k ∈ Finset.Ioc loI hiI,
      a k ≠ 0 → Nat.Coprime k q)
    (h1 : ∀ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ T₁ →
      ‖∑ k ∈ (Finset.Ioc loI hiI).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (a k * χ (k : ZMod q) - Thm2.delta χ * w₁)‖ ≤ M₁)
    (h4 : ∀ n ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, ∀ χ : DirichletCharacter ℂ n, ∀ t : ℝ, t ≤ T₂ →
      ‖∑ m ∈ (Finset.Ioc loJ hiJ).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (b m * χ (m : ZMod n) - Thm2.delta χ * w₂)‖ ≤ M₂)
    (hV : ∑ m ∈ Finset.Ioc loJ hiJ, ‖b m‖ ≤ V) :
    ‖(∫ t in Ioc (1 / (Q : ℝ)) (1 + 1 / (Q : ℝ)) ∩ ⋃ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊,
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Icc ((r : ℝ) / q - T ^ 4 / (q * Y)) ((r : ℝ) / q + T ^ 4 / (q * Y)),
        (∑ k ∈ Finset.Ioc loI hiI, a k * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
          (∑ m ∈ Finset.Ioc loJ hiJ, b m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
            @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) -
      w₁ * w₂ * ∑ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊,
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
          ∫ η in (-(T ^ 4 / (q * Y)))..(T ^ 4 / (q * Y)),
            (∑ k ∈ Finset.Ioc loI hiI, (1 : ℂ) * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) *
              (∑ m ∈ Finset.Ioc loJ hiJ, (1 : ℂ) * @fourier 1 (m : ℤ) (η : AddCircle (1 : ℝ))) *
                @fourier 1 (-(N : ℤ)) (η : AddCircle (1 : ℝ))‖ ≤
      40 * T ^ 12 * M₁ * V / Y + 120 * ‖w₁‖ * T ^ 16 * M₂ := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
  have hT4 : 1 ≤ T ^ 4 := one_le_pow₀ hT
  have hPle : ((⌊T ^ 2⌋₊ : ℕ) : ℝ) ≤ T ^ 2 := Nat.floor_le (by positivity)
  have hP1 : 1 ≤ ⌊T ^ 2⌋₊ := Nat.le_floor (by simpa using hT2)
  have hQpos : (0 : ℝ) < Q := by linarith
  have h1mem : 1 ∈ Finset.Icc 1 ⌊T ^ 2⌋₊ := Finset.mem_Icc.mpr ⟨le_rfl, hP1⟩
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (h1 1 h1mem 1 T₁ le_rfl)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h4 1 h1mem 1 T₂ le_rfl)
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun m _ => norm_nonneg _).trans hV
  have hT48 : T ^ 4 ≤ T ^ 8 := pow_le_pow_right₀ hT (by norm_num)
  have hT4Y : T ^ 4 / Y < 1 / 2 := by
    rw [div_lt_iff₀ hY]
    linarith
  have hqfacts : ∀ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, (1 : ℝ) ≤ q ∧ (q : ℝ) ≤ T ^ 2 := by
    intro q hq
    have hq1 := Finset.mem_Icc.mp hq
    exact ⟨by exact_mod_cast hq1.1, le_trans (by exact_mod_cast hq1.2) hPle⟩
  have hhle : ∀ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, T ^ 4 / ((q : ℝ) * Y) ≤ T ^ 4 / Y := by
    intro q hq
    obtain ⟨hq1, _⟩ := hqfacts q hq
    exact div_le_div_of_nonneg_left (by positivity) hY (by nlinarith)
  have hh : ∀ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, 0 ≤ T ^ 4 / ((q : ℝ) * Y) := by
    intro q hq
    have := (hqfacts q hq).1
    positivity
  have hsmall : ∀ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊,
      2 * (T ^ 4 / ((q : ℝ) * Y)) * ((⌊T ^ 2⌋₊ : ℕ) : ℝ) ^ 2 < 1 := by
    intro q hq
    have h5 : ((⌊T ^ 2⌋₊ : ℕ) : ℝ) ^ 2 ≤ (T ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hPle 2
    calc
      _ ≤ 2 * (T ^ 4 / Y) * (T ^ 2) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hhle q hq) (by norm_num)) h5 (by positivity)
          (by positivity)
      _ = 2 * T ^ 8 / Y := by ring
      _ < 1 := by
        rw [div_lt_one hY]
        exact hc2
  have hinside : ∀ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊,
      ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        1 / (Q : ℝ) < (r : ℝ) / q - T ^ 4 / ((q : ℝ) * Y) ∧
          (r : ℝ) / q + T ^ 4 / ((q : ℝ) * Y) ≤ 1 + 1 / (Q : ℝ) := by
    intro q hq r hr
    obtain ⟨hq1, hqT⟩ := hqfacts q hq
    have hrm := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrm.1
    have hrq : (r : ℝ) ≤ q := by exact_mod_cast hrm.2
    have hqpos : (0 : ℝ) < q := by linarith
    constructor
    · have e : (r : ℝ) / q - T ^ 4 / ((q : ℝ) * Y) = (r - T ^ 4 / Y) / q := by
        field_simp
      rw [e, div_lt_div_iff₀ hQpos hqpos]
      have h5 : (1 / 2 : ℝ) * Q < (r - T ^ 4 / Y) * Q :=
        mul_lt_mul_of_pos_right (by linarith) hQpos
      linarith
    · have h5 : (r : ℝ) / q ≤ 1 := (div_le_one hqpos).mpr hrq
      have h6 : T ^ 4 / Y ≤ 1 / (Q : ℝ) := by
        rw [div_le_div_iff₀ hY hQpos]
        linarith
      linarith [hhle q hq]
  have key := major_total512j ⌊T ^ 2⌋₊ (fun q : ℕ => T ^ 4 / ((q : ℝ) * Y)) (1 / (Q : ℝ))
    (1 + 1 / (Q : ℝ)) loI hiI loJ hiJ a b w₁ w₂ M₁ M₂ V T₁ T₂ N hT₁ hT₂ hh hsmall hinside
    hsupp h1 h4 hV
  refine key.trans ?_
  have hπ : 2 * Real.pi ≤ 19 / 3 := by linarith [Real.pi_lt_d2]
  have hB : ∀ q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊,
      (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) *
        (2 * (T ^ 4 / ((q : ℝ) * Y)) *
          (Real.sqrt q * ((1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) *
              ((hiI - loI : ℕ) : ℝ)) * M₁) * V +
            ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
              (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
                ((1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) *
                  ((hiJ - loJ : ℕ) : ℝ)) * M₂)))) ≤
        40 * T ^ 10 * M₁ * V / Y + 120 * ‖w₁‖ * T ^ 14 * M₂ := by
    intro q hq
    obtain ⟨hq1, hqT⟩ := hqfacts q hq
    have hqpos : (0 : ℝ) < q := by linarith
    have hh0 := hh q hq
    have hcard : (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) ≤ q := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    have hsq : Real.sqrt q ≤ T ^ 2 :=
      (Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩).trans hqT
    have hτ : (q.divisors.card : ℝ) ≤ T ^ 2 :=
      le_trans (by exact_mod_cast Nat.card_divisors_le_self q) hqT
    have hτ2 : (q.divisors.card : ℝ) ^ 2 ≤ (T ^ 2) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hτ 2
    have e3 : (T ^ 4 / Y) * (3 * Y) = 3 * T ^ 4 := by
      field_simp
    have hf : ∀ n : ℝ, 0 ≤ n → n ≤ 3 * Y →
        1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) * n ≤ 20 * T ^ 4 := by
      intro n hn0 hn
      have h5 : (T ^ 4 / ((q : ℝ) * Y)) * n ≤ (T ^ 4 / Y) * (3 * Y) :=
        mul_le_mul (hhle q hq) hn hn0 (by positivity)
      have h6 : 2 * Real.pi * ((T ^ 4 / ((q : ℝ) * Y)) * n) ≤ 19 / 3 * (3 * T ^ 4) := by
        rw [← e3]
        exact mul_le_mul hπ h5 (mul_nonneg hh0 hn0) (by norm_num)
      calc
        _ = 1 + 2 * Real.pi * ((T ^ 4 / ((q : ℝ) * Y)) * n) := by ring
        _ ≤ 1 + 19 / 3 * (3 * T ^ 4) := by linarith
        _ ≤ 20 * T ^ 4 := by linarith
    have hfI := hf _ (Nat.cast_nonneg _) hnI
    have hfJ := hf _ (Nat.cast_nonneg _) hnJ
    have h2π : 0 ≤ 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) :=
      mul_nonneg Real.two_pi_pos.le hh0
    have hgI : 0 ≤ 1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) * ((hiI - loI : ℕ) : ℝ) :=
      add_nonneg zero_le_one (mul_nonneg h2π (Nat.cast_nonneg _))
    have hgJ : 0 ≤ 1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) * ((hiJ - loJ : ℕ) : ℝ) :=
      add_nonneg zero_le_one (mul_nonneg h2π (Nat.cast_nonneg _))
    have hX : Real.sqrt q * ((1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) *
          ((hiI - loI : ℕ) : ℝ)) * M₁) * V ≤ T ^ 2 * (20 * T ^ 4 * M₁) * V := by
      gcongr
    have hZ : ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
          (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
            ((1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) * ((hiJ - loJ : ℕ) : ℝ)) * M₂)) ≤
        ‖w₁‖ * (3 * Y) * (T ^ 2 * (T ^ 2) ^ 2 * (20 * T ^ 4 * M₂)) := by
      gcongr
    have hXnn : 0 ≤ Real.sqrt q * ((1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) *
          ((hiI - loI : ℕ) : ℝ)) * M₁) * V :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hgI hM₁)) hV0
    have hZnn : 0 ≤ ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
          (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
            ((1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) * ((hiJ - loJ : ℕ) : ℝ)) * M₂)) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (mul_nonneg hgJ hM₂))
    have hch : (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) *
        (2 * (T ^ 4 / ((q : ℝ) * Y))) ≤ 2 * T ^ 4 / Y := by
      calc
        _ ≤ (q : ℝ) * (2 * (T ^ 4 / ((q : ℝ) * Y))) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (by norm_num) hh0)
        _ = 2 * T ^ 4 / Y := by
          field_simp
    calc
      _ = ((((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) *
            (2 * (T ^ 4 / ((q : ℝ) * Y)))) *
          (Real.sqrt q * ((1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) *
              ((hiI - loI : ℕ) : ℝ)) * M₁) * V +
            ‖w₁‖ * ((hiI - loI : ℕ) : ℝ) *
              (Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
                ((1 + 2 * Real.pi * (T ^ 4 / ((q : ℝ) * Y)) *
                  ((hiJ - loJ : ℕ) : ℝ)) * M₂))) := by ring
      _ ≤ (2 * T ^ 4 / Y) * (T ^ 2 * (20 * T ^ 4 * M₁) * V +
            ‖w₁‖ * (3 * Y) * (T ^ 2 * (T ^ 2) ^ 2 * (20 * T ^ 4 * M₂))) :=
        mul_le_mul hch (add_le_add hX hZ) (add_nonneg hXnn hZnn) (by positivity)
      _ = _ := by
        field_simp
        ring
  have hBnn : 0 ≤ 40 * T ^ 10 * M₁ * V / Y + 120 * ‖w₁‖ * T ^ 14 * M₂ := by positivity
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 ⌊T ^ 2⌋₊,
        (40 * T ^ 10 * M₁ * V / Y + 120 * ‖w₁‖ * T ^ 14 * M₂) := Finset.sum_le_sum hB
    _ = ((⌊T ^ 2⌋₊ : ℕ) : ℝ) * (40 * T ^ 10 * M₁ * V / Y + 120 * ‖w₁‖ * T ^ 14 * M₂) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp
    _ ≤ T ^ 2 * (40 * T ^ 10 * M₁ * V / Y + 120 * ‖w₁‖ * T ^ 14 * M₂) :=
      mul_le_mul_of_nonneg_right hPle hBnn
    _ = _ := by ring

end LeanLab.BHP1997.Route512Major
