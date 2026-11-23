import Mathlib
import LeanLab.HelfgottMajor.PV420Split1122

/-!
Route burst S58 round two, burst-20261122, tag pomerance-lemmas.
Split of the round one LEAFs `PV420Split1122.pomerance_lemma3` and
`PV420Split1122.pomerance_sec4`, Pomerance 2011 Lemma 3 and Section 4, quoted without proof
as Lemmas 1 and 2 of Frolenkov arXiv 1107.0381, Section 3.

Source situation: Pomerance's paper is not accessible here and Frolenkov gives no proof sketch,
only "See [11, Lemma 3]" and "See [11, §4]". The split below is a reconstruction along the
standard route: the Fourier series of |sin t|, the series sum of 1/(4k^2-1), a uniform lower
bound for the cosine partial sums sum_{j ≤ n} cos(jy)/j, and the harmonic bound. The harmonic
bound H_n < log n + γ + 1/n is PROVED from Mathlib. Numerical checks are in the notes.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVLemmas1122

open Real Finset Filter Topology

/-- Harmonic bound, the H_n step of Pomerance's proofs in the weaker form
`H_n < log n + γ + 1/n`. PROVED from Mathlib's `eulerMascheroniSeq_lt_eulerMascheroniConstant`. -/
theorem harmonic_lt (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, (1 : ℝ) / j < log n + eulerMascheroniConstant + 1 / n := by
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  unfold Real.eulerMascheroniSeq at h1
  have hH : (harmonic n : ℝ) = ∑ j ∈ Icc 1 n, (1 : ℝ) / j := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : log ((n : ℝ) + 1) ≤ log n + 1 / n := by
    have := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
    rw [Real.log_div (by positivity) hnpos.ne'] at this
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  rw [← hH]; linarith

/-- LEAF: Fourier series of |sin|, the first step of the proof of Pomerance 2011 Lemma 3:
`|sin t| = 2/π - (4/π) ∑_{k ≥ 1} cos(2kt)/(4k^2 - 1)`, written as a HasSum with k + 1 for k.
Standard, e.g. Gradshteyn and Ryzhik 1.444. Class MEDIUM. -/
theorem abs_sin_fourier (t : ℝ) :
    HasSum (fun k : ℕ => 4 / π * (cos (2 * ((k : ℝ) + 1) * t) / (4 * ((k : ℝ) + 1) ^ 2 - 1)))
      (2 / π - |sin t|) := by
  sorry

/-- The series `∑_{k ≥ 1} 1/(4k^2 - 1) = 1/2`, by telescoping
`1/(4k^2-1) = (1/(2k-1) - 1/(2k+1))/2`; used to sum the Fourier coefficients in Pomerance's
Lemma 3. PROVED: partial sums equal `1/2 - 1/(2(2N+1))`. -/
theorem series_quarter :
    HasSum (fun k : ℕ => 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) (1 / 2) := by
  have hpart : ∀ N : ℕ, ∑ k ∈ range N, 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1) =
      1 / 2 - 1 / (2 * (2 * (N : ℝ) + 1)) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [sum_range_succ, ih]
      have h1 : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < 4 * ((N : ℝ) + 1) ^ 2 - 1 := by nlinarith [(N.cast_nonneg : (0:ℝ) ≤ N)]
      push_cast
      field_simp
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · simp_rw [hpart]
    have : Tendsto (fun N : ℕ => 1 / (2 * (2 * (N : ℝ) + 1))) atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      apply Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)
      apply tendsto_atTop_add_const_right
      exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (1:ℝ)/2)).sub this
  · intro k
    have : (0 : ℝ) < 4 * ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    positivity

/-- LEAF: uniform lower bound for cosine partial sums, the step of Pomerance 2011 Lemma 3 and
Section 4 that produces the constant log 2 + O(1/n): for every real y and n ≥ 1,
`∑_{j ≤ n} cos(jy)/j ≥ -(log 2 + 2/n)`. The limit `-log |2 sin(y/2)|` is at least `-log 2`;
numerically the slack is about 1.5/n. Class HARD. -/
theorem cos_partial_lower (y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    -(log 2 + 2 / n) ≤ ∑ j ∈ Icc 1 n, cos (j * y) / j := by
  sorry

/-- Partial summation step of Pomerance Lemma 3: insert the Fourier series of |sin| into the
sum over j, interchange the finite and infinite sums, and bound each cosine partial sum below.
PROVED from the three LEAFs above. -/
theorem sin_sum_le (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, |sin (j * x)| / j ≤
      2 / π * ∑ j ∈ Icc 1 n, (1 : ℝ) / j + 2 / π * (log 2 + 2 / n) := by
  set c : ℝ := log 2 + 2 / n
  set f : ℕ → ℝ → ℝ := fun k t =>
    4 / π * (cos (2 * ((k : ℝ) + 1) * t) / (4 * ((k : ℝ) + 1) ^ 2 - 1)) with hf
  -- the sum over j of the Fourier tails
  have hT : HasSum (fun k : ℕ => ∑ j ∈ Icc 1 n, f k (j * x) / j)
      (∑ j ∈ Icc 1 n, (2 / π - |sin (j * x)|) / j) :=
    hasSum_sum fun j _ => (abs_sin_fourier (j * x)).div_const _
  have hL : HasSum (fun k : ℕ => 4 / π * (-c) * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)))
      (4 / π * (-c) * (1 / 2)) := series_quarter.mul_left _
  have hle : ∀ k : ℕ, 4 / π * (-c) * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) ≤
      ∑ j ∈ Icc 1 n, f k (j * x) / j := by
    intro k
    have hd : (0 : ℝ) < 4 * ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have hrw : ∑ j ∈ Icc 1 n, f k (j * x) / j =
        4 / π * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) *
          ∑ j ∈ Icc 1 n, cos (j * (2 * ((k : ℝ) + 1) * x)) / j := by
      rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
      simp only [hf]
      have : 2 * ((k : ℝ) + 1) * (j * x) = j * (2 * ((k : ℝ) + 1) * x) := by ring
      rw [this]; ring
    rw [hrw]
    have hcl := cos_partial_lower (2 * ((k : ℝ) + 1) * x) n hn
    have hpos : 0 ≤ 4 / π * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) := by
      have := Real.pi_pos; positivity
    nlinarith
  have hbound := hasSum_le hle hL hT
  have hsplit : ∑ j ∈ Icc 1 n, (2 / π - |sin (j * x)|) / j =
      2 / π * ∑ j ∈ Icc 1 n, (1 : ℝ) / j - ∑ j ∈ Icc 1 n, |sin (j * x)| / j := by
    rw [mul_sum, ← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_; ring
  rw [hsplit] at hbound
  have e : 4 / π * (-c) * (1 / 2) = -(2 / π * c) := by ring
  linarith

/-- Assembly: exactly the round one LEAF `PV420Split1122.pomerance_lemma3`. -/
theorem pomerance_lemma3 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n) := by
  have h1 := sin_sum_le x n hn
  have h2 := harmonic_lt n hn
  have hp : 0 < 2 / π := by have := Real.pi_pos; positivity
  have h3 : 2 / π * ∑ j ∈ Icc 1 n, (1 : ℝ) / j <
      2 / π * (log n + eulerMascheroniConstant + 1 / n) := mul_lt_mul_of_pos_left h2 hp
  have e : (3 : ℝ) / n = 1 / n + 2 / n := by ring
  rw [e]; nlinarith

example : type_of% @pomerance_lemma3 =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_lemma3 := rfl

/-- LEAF: Pomerance 2011 Section 4 after removal of the harmonic sum: for all real α, β and
n ≥ 1, `∑_{m ≤ n} |cos mα - cos mβ|/m ≤ H_n + log 2 + 2/n`. At β = 0 the left side is
`H_n - ∑ cos(mα)/m`, so this is sharp up to O(1/n) against `cos_partial_lower`; numerically the
slack equals that of `cos_partial_lower`. Class HARD. -/
theorem sec4_core (α β : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m ≤
      ∑ m ∈ Icc 1 n, (1 : ℝ) / m + (log 2 + 2 / n) := by
  sorry

/-- Assembly: exactly the round one LEAF `PV420Split1122.pomerance_sec4`. -/
theorem pomerance_sec4 (α β : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n := by
  have h1 := sec4_core α β n hn
  have h2 := harmonic_lt n hn
  have e : (3 : ℝ) / n = 1 / n + 2 / n := by ring
  rw [e]; linarith

example : type_of% @pomerance_sec4 =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_sec4 := rfl

end LeanLab.HelfgottMajor.PVLemmas1122

#print axioms LeanLab.HelfgottMajor.PVLemmas1122.harmonic_lt
#print axioms LeanLab.HelfgottMajor.PVLemmas1122.abs_sin_fourier
#print axioms LeanLab.HelfgottMajor.PVLemmas1122.series_quarter
#print axioms LeanLab.HelfgottMajor.PVLemmas1122.cos_partial_lower
#print axioms LeanLab.HelfgottMajor.PVLemmas1122.sin_sum_le
#print axioms LeanLab.HelfgottMajor.PVLemmas1122.pomerance_lemma3
#print axioms LeanLab.HelfgottMajor.PVLemmas1122.sec4_core
#print axioms LeanLab.HelfgottMajor.PVLemmas1122.pomerance_sec4
