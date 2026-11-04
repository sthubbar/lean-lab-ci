/-
Elementary singular-series inputs from P0079 pages 5 to 7.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Statements

open Real Finset

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 2, display 5. Each odd-prime factor is at least one. -/
theorem Sprime_factor_one_le293 (p : ℕ) (hp : 2 < p) :
    1 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have h : (2 : ℝ) < p := by exact_mod_cast hp
  exact (one_le_div (by linarith)).mpr (by linarith)

/-- P0079 page 2, display 5. The empty product convention includes n equal to zero. -/
theorem Sprime_one_le293 (n : ℕ) : 1 ≤ Sprime n := by
  exact one_le_prod₀ (fun p hp => Sprime_factor_one_le293 p (mem_filter.mp hp).2)

/-- P0079 page 2, display 5. Every singular-series factor is positive. -/
theorem Sprime_pos293 (n : ℕ) : 0 < Sprime n := by
  linarith [Sprime_one_le293 n]

/-- P0079 page 5 after display 21. Sprime is multiplicative on coprime inputs. -/
theorem Sprime_mul_coprime293 (m n : ℕ) (h : m.Coprime n) :
    Sprime (m * n) = Sprime m * Sprime n := by
  unfold Sprime
  rw [h.primeFactors_mul, filter_union,
    prod_union (h.disjoint_primeFactors.mono (filter_subset _ _) (filter_subset _ _))]

/-- P0079 page 7 after display 27. Dividing a nonzero argument cannot increase Sprime. -/
theorem Sprime_dvd_le293 (m n : ℕ) (h : m ∣ n) (hn : n ≠ 0) : Sprime m ≤ Sprime n := by
  unfold Sprime
  apply prod_le_prod_of_subset_of_one_le₀
    (filter_subset_filter _ (Nat.primeFactors_mono h hn))
  · intro p hp
    exact le_trans (by norm_num) (Sprime_factor_one_le293 p (mem_filter.mp hp).2)
  · intro p hp _
    exact Sprime_factor_one_le293 p (mem_filter.mp hp).2

/-- P0079 page 7 after display 27. A factor of two does not change Sprime. -/
theorem Sprime_two_mul293 (n : ℕ) : Sprime (2 * n) = Sprime n := by
  by_cases hn : n = 0
  · simp [hn]
  unfold Sprime
  rw [Nat.primeFactors_mul (by norm_num) hn, Nat.prime_two.primeFactors, filter_union]
  simp only [filter_singleton, show ¬(2 < (2 : ℕ)) by omega, ite_false, empty_union]

/-- P0079 page 7 after display 27. Any power of two can be removed from Sprime. -/
theorem Sprime_two_pow_mul293 (k n : ℕ) : Sprime (2 ^ k * n) = Sprime n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 ^ (k + 1) * n = 2 * (2 ^ k * n) by ring, Sprime_two_mul293, ih]

/-- P0079 page 7, display 24. A nonzero real multiple of an integer has
no nonzero value in a shorter interval than its lattice spacing. -/
theorem int_lattice_lt_iff293 (c η : ℝ) (hc : c ≠ 0) (hη : 0 < η)
    (hηc : η < |c|) (z : ℤ) : |c * (z : ℝ)| < η ↔ z = 0 := by
  constructor
  · intro h
    rw [abs_mul] at h
    have hz : |(z : ℝ)| < 1 := by
      apply (mul_lt_mul_iff_right₀ (abs_pos.mpr hc)).mp
      simpa using h.trans hηc
    have hz' : |z| < 1 := by exact_mod_cast hz
    exact Int.abs_lt_one_iff.mp hz'
  · rintro rfl
    simpa using hη

/-- P0079 pages 6 to 7, display 24. For a rational coefficient ratio,
the small real inequality is exactly a lattice equation. -/
theorem rational_lattice_lt_iff293 (l μ η : ℝ) (a q u v : ℤ)
    (hl : l ≠ 0) (hμ : μ ≠ 0) (ha : a ≠ 0) (hq : q ≠ 0)
    (hr : l / μ = (a : ℝ) / q) (hη : 0 < η) (hηa : η < |l / a|) :
    |l * u + μ * v| < η ↔ l * u + μ * v = 0 := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hm : μ = l / a * q := by
    field_simp at hr ⊢
    nlinarith only [hr]
  have heq : l * u + μ * v = (l / a) * ((a * u + q * v : ℤ) : ℝ) := by
    push_cast
    rw [hm]
    field_simp
  rw [heq, int_lattice_lt_iff293 (l / a) η (div_ne_zero hl haR) hη hηa]
  rw [mul_eq_zero, or_iff_right (div_ne_zero hl haR)]
  exact Int.cast_eq_zero.symm

/-- P0079 page 2, display 4. Cq is symmetric in its two denominators. -/
theorem Cq_comm293 (q1 q2 : ℕ) : Cq q1 q2 = Cq q2 q1 := by
  exact mul_comm _ _

/-- P0079 page 2, display 4. Cq is positive for every pair of denominators. -/
theorem Cq_pos293 (q1 q2 : ℕ) : 0 < Cq q1 q2 := by
  have hc : 0 < bigC := by norm_num [bigC]
  have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
  exact mul_pos (sqrt_pos.mpr (add_pos hl (mul_pos hc (Sprime_pos293 q1))))
    (sqrt_pos.mpr (add_pos hl (mul_pos hc (Sprime_pos293 q2))))

/-- P0079 page 7 after display 27. Sprime of a product of nonzero inputs
is at most the product of their Sprime values. -/
theorem Sprime_mul_le293 (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Sprime (m * n) ≤ Sprime m * Sprime n := by
  let A := m.primeFactors.filter (fun p => 2 < p)
  let B := n.primeFactors.filter (fun p => 2 < p)
  let f := fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2)
  have hfactor : ∀ p ∈ A ∪ B, 1 ≤ f p := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact Sprime_factor_one_le293 p (mem_filter.mp hp).2
    · exact Sprime_factor_one_le293 p (mem_filter.mp hp).2
  have hu : 0 ≤ ∏ p ∈ A ∪ B, f p :=
    le_trans (by norm_num) (one_le_prod₀ hfactor)
  have hi : 1 ≤ ∏ p ∈ A ∩ B, f p :=
    one_le_prod₀ (fun p hp => hfactor p (mem_union_left _ (mem_inter.mp hp).1))
  have H := mul_le_mul_of_nonneg_left hi hu
  rw [mul_one, prod_union_inter] at H
  simpa only [Sprime, Nat.primeFactors_mul hm hn, filter_union, A, B, f] using H

/-- P0079 page 2, the Theorem's literal first lattice bound.
A positive tolerance under that bound forces a positive reduced numerator. -/
theorem first_num_pos293 (l1 η : ℝ) (r : ℚ) (h1 : 0 < l1) (hη : 0 < η)
    (hlt : η < l1 / r.num) : 0 < r.num := by
  have hnum : (0 : ℝ) < r.num := (div_pos_iff_of_pos_left h1).mp (hη.trans hlt)
  exact_mod_cast hnum

/-- P0079 page 2, the Theorem's literal first lattice bound and rationality condition.
These hypotheses force the paired first power coefficient to be positive. -/
theorem first_mu_pos293 (l1 μ η : ℝ) (r : ℚ) (h1 : 0 < l1) (hη : 0 < η)
    (hlt : η < l1 / r.num) (hr : (r : ℝ) = l1 / μ) : 0 < μ := by
  have hnum := first_num_pos293 l1 η r h1 hη hlt
  have hrpos : (0 : ℝ) < r := by
    rw [Rat.cast_def]
    exact div_pos (by exact_mod_cast hnum) (by exact_mod_cast r.den_pos)
  rw [hr] at hrpos
  exact (div_pos_iff_of_pos_left h1).mp hrpos

end LeanLab.LZPowersOfTwo
