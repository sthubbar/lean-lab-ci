/-
ROUTE BURST burst-20261122, session S81. Elementary PROVED pieces toward the two MEDIUM LEAFs
of KernelSumSplit1122, P0088 Kumchev and Liu 2007, page 7, the display before 27.
* sq_gap: squares m^2 and m'^2 with m at most m' differ by at least 2 m times m' - m, the
  spacing count input of outer_square_bound.
* edgeDecay_le_one, edgeDecay_nonneg: range of the decay weight.
* two_sin_mul_sum_sin, abs_sin_mul_sum_le: the telescoping identity and the Abel summation
  input |sin x| times |sum of sin 2 (M + j) x| at most 1, which gives partial sums of
  sin 2 pi k b of size O of 1/b, the core of inner_window_bound.
* Kb_zero, Kb_abs_le: the kernel is 1 - 2b at zero and at most 1/(pi |k|) elsewhere.
* abs_sum_sin_le: partial sums of sin 2 pi k b are at most 1/(2b) for 0 < b at most 1/2.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelBase687

namespace LeanLab.KumchevLiu2007.KernelSumPieces1122

open Real LeanLab.KumchevLiu2007.KernelSumSplit1122
open scoped BigOperators

/-- PROVED. Spacing of squares: (m' - m) 2m at most m'^2 - m^2 for m at most m'. -/
theorem sq_gap (m m' : ℕ) (h : m ≤ m') :
    ((m' : ℝ) - m) * (2 * m) ≤ (m' : ℝ) ^ 2 - (m : ℝ) ^ 2 := by
  have h' : (m : ℝ) ≤ m' := by exact_mod_cast h
  nlinarith [sq_nonneg ((m' : ℝ) - m)]

/-- PROVED. The decay weight is at most one. -/
theorem edgeDecay_le_one (X Y b : ℝ) (n m2 : ℕ) : edgeDecay X Y b n m2 ≤ 1 :=
  min_le_left _ _

/-- PROVED. The decay weight is nonnegative for b at least zero. -/
theorem edgeDecay_nonneg (X Y b : ℝ) (n m2 : ℕ) (hb : 0 ≤ b) : 0 ≤ edgeDecay X Y b n m2 := by
  unfold edgeDecay
  refine le_min zero_le_one (div_nonneg zero_le_one (mul_nonneg hb ?_))
  exact add_nonneg (le_min (abs_nonneg _) (abs_nonneg _)) zero_le_one

/-- PROVED. Product to sum: 2 sin x sin y = cos (x - y) - cos (x + y). -/
theorem two_sin_mul_sin (x y : ℝ) : 2 * Real.sin x * Real.sin y =
    Real.cos (x - y) - Real.cos (x + y) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- PROVED. Telescoping: 2 sin x times the sum over j below N of sin 2 (M + j) x equals
cos (2M - 1) x minus cos (2 (M + N) - 1) x. -/
theorem two_sin_mul_sum_sin (x M : ℝ) (N : ℕ) :
    2 * Real.sin x * ∑ j ∈ Finset.range N, Real.sin (2 * (M + j) * x) =
      Real.cos ((2 * M - 1) * x) - Real.cos ((2 * (M + N) - 1) * x) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, two_sin_mul_sin]
    have h1 : x - 2 * (M + N) * x = -((2 * (M + N) - 1) * x) := by ring
    have h2 : x + 2 * (M + N) * x = (2 * (M + ((N + 1 : ℕ) : ℝ)) - 1) * x := by
      push_cast; ring
    rw [h1, h2, Real.cos_neg]; ring

/-- PROVED. Abel summation input: |sin x| times |sum over j below N of sin 2 (M + j) x| is at
most one. With x = pi b this bounds partial sums of sin 2 pi k b by 1/sin pi b. -/
theorem abs_sin_mul_sum_le (x M : ℝ) (N : ℕ) :
    |Real.sin x| * |∑ j ∈ Finset.range N, Real.sin (2 * (M + j) * x)| ≤ 1 := by
  have h := two_sin_mul_sum_sin x M N
  set S := ∑ j ∈ Finset.range N, Real.sin (2 * (M + j) * x)
  have hb : |2 * Real.sin x * S| ≤ 2 := by
    rw [h, abs_le]
    have a1 := Real.neg_one_le_cos ((2 * M - 1) * x)
    have a2 := Real.cos_le_one ((2 * M - 1) * x)
    have a3 := Real.neg_one_le_cos ((2 * (M + N) - 1) * x)
    have a4 := Real.cos_le_one ((2 * (M + N) - 1) * x)
    constructor <;> linarith
  rw [abs_mul, abs_mul, abs_two] at hb
  linarith

/-- PROVED. Partial sums of sin 2 pi k b over any run of consecutive k are at most 1/(2b) for
0 < b at most 1/2, by abs_sin_mul_sum_le and Jordan's inequality sin pi b at least 2b. -/
theorem abs_sum_sin_le (b M : ℝ) (N : ℕ) (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    |∑ j ∈ Finset.range N, Real.sin (2 * (M + j) * (π * b))| ≤ 1 / (2 * b) := by
  have hpi := Real.pi_pos
  have hs : 2 * b ≤ Real.sin (π * b) := by
    have h0 := Real.mul_le_sin (x := π * b) (by positivity) (by nlinarith)
    have e : 2 / π * (π * b) = 2 * b := by field_simp
    linarith
  have h := abs_sin_mul_sum_le (π * b) M N
  set S := ∑ j ∈ Finset.range N, Real.sin (2 * (M + j) * (π * b))
  rw [abs_of_pos (by linarith : 0 < Real.sin (π * b))] at h
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg S)]

/-- PROVED. The kernel at zero is 1 - 2b. -/
theorem Kb_zero (b : ℝ) : Kb b 0 = 1 - 2 * b := by
  simp [Kb]

/-- PROVED. Away from zero the kernel is -sin(2 pi k b)/(pi k), of size at most 1/(pi |k|). -/
theorem Kb_abs_le (b : ℝ) (k : ℤ) (hk : k ≠ 0) : |Kb b k| ≤ 1 / (π * |(k : ℝ)|) := by
  have hpi := Real.pi_pos
  have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have e : Kb b k = -(Real.sin (2 * π * (k : ℝ) * b) / (π * (k : ℝ))) := by
    simp [Kb, hk]
  rw [e, abs_neg, abs_div, abs_mul, abs_of_pos hpi]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

end LeanLab.KumchevLiu2007.KernelSumPieces1122

#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.sq_gap
#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.edgeDecay_le_one
#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.edgeDecay_nonneg
#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.two_sin_mul_sin
#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.two_sin_mul_sum_sin
#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.abs_sin_mul_sum_le
#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.abs_sum_sin_le
#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.Kb_zero
#print axioms LeanLab.KumchevLiu2007.KernelSumPieces1122.Kb_abs_le
