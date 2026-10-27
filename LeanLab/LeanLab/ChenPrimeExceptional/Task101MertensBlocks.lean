/-
AI wrote this Lean code for CODEX task101.
P0039 equation 3.7 and pages 66 to 67. Actual Mertens normalization blocks.
Binary Goldbach is open.
-/
import LeanLab.PNTSieve.MertensLower
import LeanLab.PNTSieve.MertensProduct

open Finset Real

namespace LeanLab.ChenPrimeExceptional.Task101

open LeanLab.PNTSieve.Mertens

noncomputable section

/-- Partial summation on a block of natural endpoints. -/
theorem abel_block {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    E w - E y = C w / log w - C y / log y +
      ∑ n ∈ Ico y w, C n * (1 / log n - 1 / log ((n : ℝ) + 1)) := by
  have hs := sum_Ico_consecutive (f := fun n : ℕ =>
    C n * (1 / log n - 1 / log ((n : ℝ) + 1))) hy hyw
  rw [abel w (by omega), abel y hy]
  linarith

/-- A logarithm lies between the left and right reciprocal rectangles. -/
theorem log_reciprocal_rectangles {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x * (1 / x - 1 / y) ≤ log y - log x ∧
      log y - log x ≤ y * (1 / x - 1 / y) := by
  have hy : 0 < y := hx.trans_le hxy
  have hl := one_sub_inv_le_log_of_pos (div_pos hy hx)
  have hu := log_le_sub_one_of_pos (div_pos hy hx)
  rw [log_div hy.ne' hx.ne'] at hl hu
  constructor
  · convert hl using 1; field_simp
  · convert hu using 1; field_simp

/-- The prime logarithmic sum differs from log by at most seven. -/
theorem C_log_error {n : ℕ} (hn : 2 ≤ n) : |C n - log n| ≤ 7 := by
  rw [abs_le]
  constructor <;> linarith [C_le n (by omega), C_ge n]

/-- The boundary term in partial summation has error at most seven over log n. -/
theorem C_div_log_error {n : ℕ} (hn : 2 ≤ n) :
    |C n / log n - 1| ≤ 7 / log n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hl : 0 < log n := log_pos hn'
  rw [show C n / log n - 1 = (C n - log n) / log n by field_simp, abs_div,
    abs_of_pos hl]
  exact div_le_div_of_nonneg_right (C_log_error hn) hl.le

/-- A discrete partial-summation cell has summable error. -/
theorem mertens_cell_error {n : ℕ} (hn : 2 ≤ n) :
    |C n * (1 / log n - 1 / log ((n : ℝ) + 1)) -
      (log (log ((n : ℝ) + 1)) - log (log n))| ≤
        8 * (1 / log n - 1 / log ((n : ℝ) + 1)) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hx : 0 < log n := log_pos hn'
  have hxy : log n ≤ log ((n : ℝ) + 1) := log_le_log (by linarith) (by linarith)
  have hr := log_reciprocal_rectangles hx hxy
  have hd := diff_nonneg hn
  have hC := C_log_error hn
  rw [abs_le] at hC ⊢
  have hstep : log ((n : ℝ) + 1) - log n ≤ 1 := by
    rw [← log_div (by positivity) (by positivity)]
    have hu := log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
    have ht : ((n : ℝ) + 1) / n - 1 ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ (show (0 : ℝ) < n by linarith)]
      nlinarith
    exact hu.trans ht
  have hcL := mul_le_mul_of_nonneg_right hC.1 hd
  have hcU := mul_le_mul_of_nonneg_right hC.2 hd
  have hs := mul_le_mul_of_nonneg_right hstep hd
  constructor <;> nlinarith

/-- The reciprocal-log increments telescope on any block. -/
theorem reciprocal_log_telescope {y w : ℕ} (hyw : y ≤ w) :
    (∑ n ∈ Ico y w, (1 / log n - 1 / log ((n : ℝ) + 1))) =
      1 / log y - 1 / log w := by
  simpa only [Nat.cast_add, Nat.cast_one, neg_sub_neg] using
    sum_Ico_sub (fun n : ℕ => -(1 / log n)) hyw

/-- The log-log increments telescope on any block. -/
theorem log_log_telescope {y w : ℕ} (hyw : y ≤ w) :
    (∑ n ∈ Ico y w, (log (log ((n : ℝ) + 1)) - log (log n))) =
      log (log w) - log (log y) := by
  simpa using sum_Ico_sub (fun n : ℕ => log (log n)) hyw

/-- Prime reciprocal blocks have an explicit vanishing error from the log-log difference. -/
theorem reciprocal_block_error {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    |E w - E y - (log (log w) - log (log y))| ≤ 22 / log y := by
  have hy' : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hly : 0 < log y := log_pos hy'
  have hlyw : log y ≤ log w := log_le_log (by linarith) (by exact_mod_cast hyw)
  have hw : 2 ≤ w := hy.trans hyw
  have hbw := (C_div_log_error hw).trans
    (div_le_div_of_nonneg_left (by norm_num) hly hlyw)
  have hby := C_div_log_error hy
  have hs : |∑ n ∈ Ico y w,
      (C n * (1 / log n - 1 / log ((n : ℝ) + 1)) -
        (log (log ((n : ℝ) + 1)) - log (log n)))| ≤ 8 / log y := by
    calc
      _ ≤ ∑ n ∈ Ico y w, |C n * (1 / log n - 1 / log ((n : ℝ) + 1)) -
          (log (log ((n : ℝ) + 1)) - log (log n))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Ico y w, 8 * (1 / log n - 1 / log ((n : ℝ) + 1)) := by
        apply sum_le_sum
        intro n hn
        exact mertens_cell_error (hy.trans (mem_Ico.mp hn).1)
      _ = 8 * (1 / log y - 1 / log w) := by
        rw [← mul_sum, reciprocal_log_telescope hyw]
      _ ≤ 8 / log y := by
        have : 0 ≤ 1 / log w := by positivity
        simp only [div_eq_mul_inv] at this ⊢
        linarith
  have heq : E w - E y - (log (log w) - log (log y)) =
      (C w / log w - 1) - (C y / log y - 1) +
        ∑ n ∈ Ico y w,
          (C n * (1 / log n - 1 / log ((n : ℝ) + 1)) -
            (log (log ((n : ℝ) + 1)) - log (log n))) := by
    rw [sum_sub_distrib, log_log_telescope hyw, abel_block hy hyw]
    ring
  rw [heq]
  have ht := abs_add_le ((C w / log w - 1) - (C y / log y - 1))
    (∑ n ∈ Ico y w,
      (C n * (1 / log n - 1 / log ((n : ℝ) + 1)) -
        (log (log ((n : ℝ) + 1)) - log (log n))))
  have ht2 : |(C w / log w - 1) - (C y / log y - 1)| ≤
      |C w / log w - 1| + |C y / log y - 1| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (C w / log w - 1) (-(C y / log y - 1))
  simp only [div_eq_mul_inv, one_mul] at hbw hby hs ht ht2 ⊢
  linarith

/-- The actual Euler product between two natural endpoints. -/
def eulerBlock (y w : ℕ) : ℝ :=
  ∏ p ∈ (Ioc y w).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-- The prime reciprocal sum on a block is the difference of its partial sums. -/
theorem reciprocal_block_eq {y w : ℕ} (hyw : y ≤ w) :
    ∑ p ∈ (Ioc y w).filter Nat.Prime, 1 / (p : ℝ) = E w - E y := by
  rw [E_eq, E_eq]
  simp only [sum_filter]
  have hs := sum_Ioc_consecutive (fun p : ℕ => if p.Prime then (1 : ℝ) / p else 0)
    (Nat.zero_le y) hyw
  have hI (N : ℕ) : Ioc 0 N = Icc 1 N := by ext n; simp; omega
  rw [hI, hI] at hs
  linarith

/-- Every actual Euler factor in a block above two is strictly positive. -/
theorem eulerBlock_pos {y w : ℕ} (hy : 2 ≤ y) : 0 < eulerBlock y w := by
  unfold eulerBlock
  apply prod_pos
  intro p hp
  have hpy := (mem_Ioc.mp (mem_filter.mp hp).1).1
  have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp')

/-- Each Euler logarithm differs from minus its reciprocal by a square-summable error. -/
theorem euler_log_error {p : ℕ} (hp : 2 ≤ p) :
    |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 * ((1 : ℝ) / p) ^ 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hsmall : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp'
  have hlow := log_one_sub_ge ((1 : ℝ) / p) (by positivity) hsmall
  have hhigh := log_le_sub_one_of_pos (show 0 < 1 - (1 : ℝ) / p by linarith)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((1 : ℝ) / p)]

/-- The error in replacing log of a block Euler product by minus its reciprocal sum. -/
theorem eulerBlock_log_error {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    |log (eulerBlock y w) + (E w - E y)| ≤ 2 / (y : ℝ) := by
  have hpos : ∀ p ∈ (Ioc y w).filter Nat.Prime, 0 < 1 - (1 : ℝ) / p := by
    intro p hp
    have hpy := (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp')
  rw [eulerBlock, log_prod (fun p hp => (hpos p hp).ne'), ← reciprocal_block_eq hyw,
    ← sum_add_distrib]
  calc
    _ ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime,
        |log (1 - (1 : ℝ) / p) + (1 : ℝ) / p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, 2 * ((1 : ℝ) / p) ^ 2 := by
      apply sum_le_sum
      intro p hp
      exact euler_log_error (by have := (mem_Ioc.mp (mem_filter.mp hp).1).1; omega)
    _ ≤ ∑ p ∈ Ioc y w, 2 * ((1 : ℝ) / p) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = 2 * ∑ p ∈ Ioc y w, ((p : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      simp
    _ ≤ 2 * ((y : ℝ)⁻¹ - (w : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (by omega : y ≠ 0) hyw) (by norm_num)
    _ ≤ _ := by
      have : 0 ≤ (w : ℝ)⁻¹ := by positivity
      simp only [div_eq_mul_inv]
      linarith

/-- Explicit actual Euler-product approximation for arbitrary endpoints above two. -/
theorem eulerBlock_log_ratio_error {y w : ℕ} (hy : 2 ≤ y) (hyw : y ≤ w) :
    |log (eulerBlock y w) - log (log y / log w)| ≤
      22 / log y + 2 / (y : ℝ) := by
  have hy' : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hw' : (1 : ℝ) < w := by exact_mod_cast (show 1 < w by omega)
  rw [log_div (log_pos hy').ne' (log_pos hw').ne']
  have h1 := eulerBlock_log_error hy hyw
  have h2 := reciprocal_block_error hy hyw
  have heq : log (eulerBlock y w) - (log (log y) - log (log w)) =
      (log (eulerBlock y w) + (E w - E y)) -
        (E w - E y - (log (log w) - log (log y))) := by ring
  rw [heq]
  have ht := abs_add_le (log (eulerBlock y w) + (E w - E y))
    (-(E w - E y - (log (log w) - log (log y))))
  simp only [abs_neg, ← sub_eq_add_neg] at ht
  linarith

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.abel_block
#print axioms LeanLab.ChenPrimeExceptional.Task101.log_reciprocal_rectangles
#print axioms LeanLab.ChenPrimeExceptional.Task101.C_log_error
#print axioms LeanLab.ChenPrimeExceptional.Task101.C_div_log_error
#print axioms LeanLab.ChenPrimeExceptional.Task101.mertens_cell_error
#print axioms LeanLab.ChenPrimeExceptional.Task101.reciprocal_log_telescope
#print axioms LeanLab.ChenPrimeExceptional.Task101.log_log_telescope
#print axioms LeanLab.ChenPrimeExceptional.Task101.reciprocal_block_error
#print axioms LeanLab.ChenPrimeExceptional.Task101.reciprocal_block_eq
#print axioms LeanLab.ChenPrimeExceptional.Task101.eulerBlock_pos
#print axioms LeanLab.ChenPrimeExceptional.Task101.euler_log_error
#print axioms LeanLab.ChenPrimeExceptional.Task101.eulerBlock_log_error
#print axioms LeanLab.ChenPrimeExceptional.Task101.eulerBlock_log_ratio_error
