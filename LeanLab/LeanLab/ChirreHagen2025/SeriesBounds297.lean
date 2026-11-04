import Mathlib

/-!
Elementary series comparisons in P0075 pages 5 and 6.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.SeriesBounds297

/-- P0075 page 6, first display, the two geometric majorants.
This is the exact generic comparison from Decomp272b and assumes no zeta estimate. -/
theorem differentiated_laurent_majorant (a : ℕ → ℂ) (z : ℂ) (t : ℝ)
    (ht : 0 < t) (htop : t ≤ 1 / 2)
    (hsum : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * a (n + 1) *
      ((t : ℂ) * Complex.I) ^ n) z)
    (hcoeff : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤
      (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n)) :
    ‖z‖ ≤ 4 / (2 * Real.pi - 1) + 4 / (4 * Real.pi ^ 2 - 1) := by
  let g (n : ℕ) : ℝ :=
    ((if Even (n + 1) then 4 else 2) / Real.pi ^ (n + 1)) * (1 / 2) ^ n
  have hp : 0 < Real.pi := Real.pi_pos
  have hq : |(1 : ℝ) / (4 * Real.pi ^ 2)| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    apply (div_lt_one (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hgeom := hasSum_geometric_of_abs_lt_one hq
  have hgeven : HasSum (fun n : ℕ => g (2 * n))
      ((2 / Real.pi) * (1 - 1 / (4 * Real.pi ^ 2))⁻¹) := by
    apply (hgeom.mul_left (2 / Real.pi)).congr_fun
    intro n
    dsimp [g]
    simp only [Nat.not_even_bit1, ite_false]
    rw [pow_add, pow_one, pow_mul, pow_mul]
    field_simp
    ring_nf
    simp [← mul_pow, hp.ne']
  have hgodd : HasSum (fun n : ℕ => g (2 * n + 1))
      ((2 / Real.pi ^ 2) * (1 - 1 / (4 * Real.pi ^ 2))⁻¹) := by
    apply (hgeom.mul_left (2 / Real.pi ^ 2)).congr_fun
    intro n
    dsimp [g]
    simp only [show Even (2 * n + 1 + 1) from ⟨n + 1, by omega⟩, ite_true]
    rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega, pow_add, pow_mul, pow_add, pow_one, pow_mul]
    field_simp
    ring_nf
    simp [← mul_pow, hp.ne']
  have hg := hgeven.even_add_odd hgodd
  have hterm (n : ℕ) :
      ‖((n + 1 : ℕ) : ℂ) * a (n + 1) * ((t : ℂ) * Complex.I) ^ n‖ ≤ g n := by
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hc := hcoeff (n + 1) (by omega)
    rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Complex.norm_I, mul_one]
    calc
      _ ≤ (n + 1 : ℕ) *
          ((if Even (n + 1) then 4 else 2) / (((n + 1 : ℕ) : ℝ) * Real.pi ^ (n + 1))) *
          (1 / 2) ^ n := by
        gcongr
      _ = g n := by dsimp [g]; field_simp
  have hnorm := hg.summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
  calc
    ‖z‖ = ‖∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * a (n + 1) * ((t : ℂ) * Complex.I) ^ n‖ := by
      rw [hsum.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖((n + 1 : ℕ) : ℂ) * a (n + 1) * ((t : ℂ) * Complex.I) ^ n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, g n := Summable.tsum_le_tsum hterm hnorm hg.summable
    _ = _ := hg.tsum_eq
    _ = _ := by
      have h1 : 2 * Real.pi - 1 ≠ 0 := by nlinarith [Real.pi_gt_three]
      have h2 : 4 * Real.pi ^ 2 - 1 ≠ 0 := by nlinarith [Real.pi_gt_three]
      have h3 : 1 - 1 / (4 * Real.pi ^ 2) ≠ 0 := by
        apply ne_of_gt
        apply sub_pos.mpr
        apply (div_lt_one (by positivity)).mpr
        nlinarith [Real.pi_gt_three]
      field_simp [h1, h2, h3]
      have h4 : Real.pi ^ 2 * 4 - 1 ≠ 0 := by nlinarith [Real.pi_gt_three]
      field_simp [h4]
      ring

/-- P0075 page 5, the logarithmic sums after equation 2.11.
This is the exact generic comparison from Decomp272a and assumes no zeta identity. -/
theorem laurent_log_majorant (a : ℕ → ℂ) (z : ℂ) (t : ℝ)
    (ht : 0 < t) (htop : t ≤ 1 / 2)
    (hsum : HasSum (fun n : ℕ => a n * ((t : ℂ) * Complex.I) ^ n) z)
    (hzero : ‖a 0‖ ≤ (0.578 : ℝ))
    (hcoeff : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤
      (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n)) :
    ‖z‖ ≤ 0.578 - 2 * Real.log (1 - 1 / (2 * Real.pi)) -
      Real.log (1 - 1 / (4 * Real.pi ^ 2)) := by
  let r : ℝ := 1 / (2 * Real.pi)
  have hp := Real.pi_pos
  have hr : |r| < 1 := by
    dsimp [r]
    rw [abs_of_pos (by positivity)]
    apply (div_lt_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hr2 : |r ^ 2| < 1 := by
    simpa only [abs_pow] using pow_lt_one₀ (abs_nonneg r) hr (by norm_num : (2 : ℕ) ≠ 0)
  have hb : HasSum (fun n : ℕ => r ^ n / n) (-Real.log (1 - r)) := by
    have hser : HasSum (fun n : ℕ => r ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
        (-Real.log (1 - r)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Real.hasSum_pow_div_log_of_abs_lt_one hr
    have h := (hasSum_nat_add_iff (f := fun n : ℕ => r ^ n / (n : ℝ)) 1).mp hser
    simpa only [Finset.sum_range_one, pow_zero, Nat.cast_zero, div_zero, add_zero] using h
  have hb2 : HasSum (fun n : ℕ => (r ^ 2) ^ n / n) (-Real.log (1 - r ^ 2)) := by
    have hser : HasSum (fun n : ℕ => (r ^ 2) ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
        (-Real.log (1 - r ^ 2)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Real.hasSum_pow_div_log_of_abs_lt_one hr2
    have h := (hasSum_nat_add_iff (f := fun n : ℕ => (r ^ 2) ^ n / (n : ℝ)) 1).mp hser
    simpa only [Finset.sum_range_one, pow_zero, Nat.cast_zero, div_zero, add_zero] using h
  have heven : HasSum (fun n : ℕ => if Even (2 * n) then r ^ (2 * n) / (2 * n) else 0)
      ((1 / 2) * (-Real.log (1 - r ^ 2))) := by
    apply (hb2.mul_left (1 / 2)).congr_fun
    intro n
    simp only [even_two_mul, ite_true, Nat.cast_mul, Nat.cast_ofNat, pow_mul]
    ring
  have hodd : HasSum (fun n : ℕ => if Even (2 * n + 1) then r ^ (2 * n + 1) / (2 * n + 1) else 0)
      (0 : ℝ) := by
    simpa only [Nat.not_even_bit1, ite_false] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have he : HasSum (fun n : ℕ => if Even n then r ^ n / (n : ℝ) else 0)
      ((1 / 2) * (-Real.log (1 - r ^ 2)) + 0) := by
    apply HasSum.even_add_odd
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using heven
    · simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hodd
  let g (n : ℕ) : ℝ := 2 * (r ^ n / n) +
    2 * (if Even n then r ^ n / n else 0) + if n = 0 then 0.578 else 0
  have hspike : HasSum (fun n : ℕ => if n = 0 then (0.578 : ℝ) else 0) 0.578 := hasSum_ite_eq _ _
  have hg := ((hb.mul_left 2).add (he.mul_left 2)).add hspike
  change HasSum g _ at hg
  have hterm (n : ℕ) : ‖a n * ((t : ℂ) * Complex.I) ^ n‖ ≤ g n := by
    by_cases hn : n = 0
    · subst n
      simpa [g] using hzero
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hc := hcoeff n (by omega)
    rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, Complex.norm_I, mul_one]
    calc
      _ ≤ ((if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n)) * (1 / 2) ^ n := by gcongr
      _ = g n := by
        dsimp [g, r]
        simp only [hn, ite_false]
        split_ifs <;> simp [div_pow, mul_pow] <;> field_simp <;> ring
  have hnorm := hg.summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
  calc
    ‖z‖ = ‖∑' n : ℕ, a n * ((t : ℂ) * Complex.I) ^ n‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖a n * ((t : ℂ) * Complex.I) ^ n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, g n := Summable.tsum_le_tsum hterm hnorm hg.summable
    _ = _ := hg.tsum_eq
    _ = _ := by dsimp [r]; rw [div_pow, mul_pow]; norm_num; ring

end LeanLab.ChirreHagen2025.SeriesBounds297
