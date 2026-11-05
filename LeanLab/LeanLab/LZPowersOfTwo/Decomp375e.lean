/-
P0079 page 10, elementary exponent bookkeeping for displays 36 and 37.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.ArcGeometry353

open Real Finset MeasureTheory Filter
open scoped Topology
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, display 36. The number of positive exponent tuples
bounded by L is exactly the s power of the natural floor of L. -/
theorem power_tuple_count375 (s : ℕ) (L : ℝ) :
    (Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊L⌋₊)).card = ⌊L⌋₊ ^ s := by
  simp

/-- P0079 page 10, passage from display 36 to display 34.
The floor count divided by L to the s tends to one. -/
theorem power_tuple_ratio375 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hε : 0 < ε) :
    Tendsto (fun X : ℝ => (⌊cutoff293 s μ ε X⌋₊ : ℝ) ^ s /
      (cutoff293 s μ ε X) ^ s) atTop (𝓝 1) := by
  simpa only [Function.comp_def, div_pow, one_pow] using
    ((tendsto_nat_floor_div_atTop (R := ℝ)).comp (cutoff_tendsto353 s μ ε hM hε)).pow s

/-- P0079 page 10, displays 36 and 37. The finite floor count spends only
one quarter lambda1 epsilon of the continuous geometric coefficient. -/
theorem model_floor_margin375 (s : ℕ) (μ : ℕ → ℝ) (ε l1 : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hε : 0 < ε) (hl : 1 < l1)
    (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - (13 / 4 : ℝ) * l1 * ε) * (cutoff293 s μ ε X) ^ s ≤
        (1 - 3 * l1 * ε) * (⌊cutoff293 s μ ε X⌋₊ : ℝ) ^ s := by
  have hprod : 0 < l1 * ε := by positivity
  have hsmall : 8 * l1 * ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith only [H]
  have hA : 0 < 1 - 3 * l1 * ε := by linarith only [hsmall]
  have hr : (1 - (13 / 4 : ℝ) * l1 * ε) / (1 - 3 * l1 * ε) < 1 := by
    apply (div_lt_one hA).mpr
    nlinarith only [hprod]
  filter_upwards [(power_tuple_ratio375 s μ ε hM hε).eventually (eventually_gt_nhds hr),
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (1 : ℝ))]
      with X hratio hL
  have hLp : 0 < (cutoff293 s μ ε X) ^ s := pow_pos (by linarith) _
  have H := (div_lt_div_iff₀ hA hLp).mp hratio
  nlinarith only [H]

/-- P0079 page 10, immediately after display 37. The definition of L
bounds every allowed power shift by epsilon X once twice absolute gamma
is at most epsilon X. No prime or irrationality hypothesis is needed. -/
theorem power_shift_bound375 (s : ℕ) (μ : ℕ → ℝ) (ε X γ : ℝ) (m : Fin s → ℕ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hε : 0 < ε) (hX : 0 < X)
    (hm : ∀ i, (m i : ℝ) ≤ cutoff293 s μ ε X) (hγ : 2 * |γ| ≤ ε * X) :
    |(∑ i : Fin s, μ i * 2 ^ m i) + γ| ≤ ε * X := by
  have hpow (i : Fin s) : (2 : ℝ) ^ m i ≤ ε * X / (2 * ∑ j : Fin s, |μ j|) := by
    rw [← Real.rpow_natCast]
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (hm i)).trans_eq ?_
    exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  calc
    _ ≤ |∑ i : Fin s, μ i * 2 ^ m i| + |γ| := abs_add_le _ _
    _ ≤ (∑ i : Fin s, |μ i * 2 ^ m i|) + |γ| := add_le_add (abs_sum_le_sum_abs _ _) le_rfl
    _ = (∑ i : Fin s, |μ i| * (2 : ℝ) ^ m i) + |γ| := by
      simp only [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
    _ ≤ (∑ i : Fin s, |μ i| * (ε * X / (2 * ∑ j : Fin s, |μ j|))) + |γ| := by
      exact add_le_add (sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hpow i) (abs_nonneg _))) le_rfl
    _ = ε * X / 2 + |γ| := by rw [← sum_mul]; congr 1; field_simp
    _ ≤ _ := by linarith only [hγ]

end LeanLab.LZPowersOfTwo
