/-
P0044, Cai 2002, page 603. The coefficient in the switched sieve.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.Cai2002.Numerics
open Finset Real
namespace LeanLab.Cai2002
/-- The prime product representation is unique across separated prime ranges.
This is the uniqueness used for g on page 603 after display 4.10. -/
theorem separated_prime_product_unique118 (z : ℝ) (p q r t : ℕ) (hp : p.Prime) (_hq : q.Prime)
    (hr : r.Prime) (ht : t.Prime) (hpz : (p : ℝ) < z) (_hqz : z ≤ (q : ℝ))
    (hrz : (r : ℝ) < z) (htz : z ≤ (t : ℝ)) (heq : p * q = r * t) :
    p = r ∧ q = t := by
  have hdiv : p ∣ r * t := by rw [← heq]; exact dvd_mul_right p q
  rcases hp.dvd_mul.mp hdiv with hpr | hpt
  · have hpr' : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
    subst r
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos heq⟩
  · have hpt' : p = t := (Nat.prime_dvd_prime_iff_eq hp ht).mp hpt
    subst t
    linarith
/-- The representation count g of page 603 for an arbitrary finite set of admissible pairs. -/
def pairMultiplicity118 (T : Finset (ℕ × ℕ)) (a : ℕ) : ℕ :=
  (T.filter (fun b => b.1 * b.2 = a)).card
/-- Page 603: the switched coefficient g is at most one. -/
theorem pairMultiplicity118_le_one (T : Finset (ℕ × ℕ)) (z : ℝ)
    (hT : ∀ b ∈ T, b.1.Prime ∧ b.2.Prime ∧ (b.1 : ℝ) < z ∧ z ≤ (b.2 : ℝ))
    (a : ℕ) : pairMultiplicity118 T a ≤ 1 := by
  unfold pairMultiplicity118
  apply card_le_one.mpr
  intro b hb c hc
  obtain ⟨hbT, hba⟩ := mem_filter.mp hb
  obtain ⟨hcT, hca⟩ := mem_filter.mp hc
  obtain ⟨hb1, hb2, hbz, hzb⟩ := hT b hbT
  obtain ⟨hc1, hc2, hcz, hzc⟩ := hT c hcT
  have heq := separated_prime_product_unique118 z b.1 b.2 c.1 c.2
    hb1 hb2 hc1 hc2 hbz hzb hcz hzc (hba.trans hca.symm)
  exact Prod.ext heq.1 heq.2

/-- Page 599 Lemma 4 coefficient condition, verified for the coefficient of page 603.
The square sum is bounded by the ordinary harmonic number uniformly in the pair set. -/
theorem pairMultiplicity118_harmonic (T : Finset (ℕ × ℕ)) (z : ℝ)
    (hT : ∀ b ∈ T, b.1.Prime ∧ b.2.Prime ∧ (b.1 : ℝ) < z ∧ z ≤ (b.2 : ℝ))
    (M : ℕ) :
    ∑ a ∈ Icc 1 M, (pairMultiplicity118 T a : ℝ) ^ 2 / (a : ℝ) ≤ harmonic M := by
  calc
    ∑ a ∈ Icc 1 M, (pairMultiplicity118 T a : ℝ) ^ 2 / (a : ℝ) ≤
        ∑ a ∈ Icc 1 M, (a : ℝ)⁻¹ := by
      apply sum_le_sum
      intro a ha
      rw [← one_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg a)
      have hg : (pairMultiplicity118 T a : ℝ) ≤ 1 := by
        exact_mod_cast pairMultiplicity118_le_one T z hT a
      have hg0 := Nat.cast_nonneg (α := ℝ) (pairMultiplicity118 T a)
      nlinarith
    _ = harmonic M := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Page 599 Lemma 4: the switched coefficient satisfies its square-sum hypothesis
with exponent one, constant two, and the uniform threshold exp one. -/
theorem pairMultiplicity118_log_bound (T : Finset (ℕ × ℕ)) (z : ℝ)
    (hT : ∀ b ∈ T, b.1.Prime ∧ b.2.Prime ∧ (b.1 : ℝ) < z ∧ z ≤ (b.2 : ℝ))
    (x : ℝ) (hx : Real.exp 1 ≤ x) :
    ∑ a ∈ Icc 1 ⌊x⌋₊, (pairMultiplicity118 T a : ℝ) ^ 2 / (a : ℝ) ≤ 2 * Real.log x := by
  have hx1 : 1 ≤ x := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hlog : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  calc
    _ ≤ (harmonic ⌊x⌋₊ : ℝ) := pairMultiplicity118_harmonic T z hT _
    _ ≤ 1 + Real.log x := harmonic_floor_le_one_add_log x hx1
    _ ≤ 2 * Real.log x := by linarith

/-- Page 602, the actual range of e in the switched pair set.
The hypotheses are the printed cutoffs for p1 and p2. -/
theorem switched_product_range118 (N p q : ℝ) (hN : 1 < N)
    (hp1 : N ^ (1 / 11 : ℝ) ≤ p) (hp2 : p < N ^ (1 / 3.29 : ℝ))
    (hq1 : N ^ (1 / 3.29 : ℝ) ≤ q) (hq2 : q < (N / p) ^ (1 / 2 : ℝ)) :
    N ^ (1 / 3 : ℝ) < p * q ∧ p * q < N ^ (2 / 3 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hp0 : 0 < p := (rpow_pos_of_pos hN0 _).trans_le hp1
  have hq0 : 0 < q := (rpow_pos_of_pos hN0 _).trans_le hq1
  constructor
  · calc
      N ^ (1 / 3 : ℝ) < N ^ (1 / 11 + 1 / 3.29 : ℝ) :=
        rpow_lt_rpow_of_exponent_lt hN E_range.1
      _ = N ^ (1 / 11 : ℝ) * N ^ (1 / 3.29 : ℝ) := rpow_add hN0 _ _
      _ ≤ p * q := mul_le_mul hp1 hq1 (rpow_pos_of_pos hN0 _).le hp0.le
  · have hroot : ((N / p) ^ (1 / 2 : ℝ)) ^ 2 = N / p := by
      rw [← rpow_natCast, ← rpow_mul (div_nonneg hN0.le hp0.le)]
      norm_num
    have hqSq : q ^ 2 < N / p := by
      rw [← hroot]
      nlinarith [rpow_pos_of_pos (div_pos hN0 hp0) (1 / 2 : ℝ)]
    have hproduct : (p * q) ^ 2 < N * p := by
      have h := mul_lt_mul_of_pos_left hqSq (sq_pos_of_pos hp0)
      have hcancel : p ^ 2 * (N / p) = N * p := by field_simp
      rw [hcancel] at h
      nlinarith
    have hupper : N * p < (N ^ (2 / 3 : ℝ)) ^ 2 := by
      calc
        N * p < N * N ^ (1 / 3.29 : ℝ) := mul_lt_mul_of_pos_left hp2 hN0
        _ = N ^ (1 + 1 / 3.29 : ℝ) := by rw [rpow_add hN0, rpow_one]
        _ < N ^ (4 / 3 : ℝ) := rpow_lt_rpow_of_exponent_lt hN (by norm_num)
        _ = (N ^ (2 / 3 : ℝ)) ^ 2 := by
          rw [← rpow_natCast, ← rpow_mul hN0.le]
          norm_num
    nlinarith [rpow_pos_of_pos hN0 (2 / 3 : ℝ)]

end LeanLab.Cai2002
