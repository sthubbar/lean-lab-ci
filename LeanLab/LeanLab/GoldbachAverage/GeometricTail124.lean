import Mathlib

/-!
P0051 page 11, the conversion from exponential weights to geometric prefix sums.
The blocks partition the positive half line exactly, including their endpoints.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.GeometricTail124
open MeasureTheory Set Filter Function

/-- Positive blocks of length N used in the page 11 geometric tail argument. -/
def block (N : ℝ) (j : ℕ) : Set ℝ := Ioi 0 ∩ Ico ((j : ℝ) * N) (((j : ℝ) + 1) * N)

/-- The exponential weight on the jth block is at most one half to the jth power.
Source: P0051 page 11, the display preceding eq. 56. -/
theorem exp_block_bound {N x : ℝ} (hN : 0 < N) (j : ℕ) (hj : (j : ℝ) * N ≤ x) :
    Real.exp (-2 * x / N) ≤ (1 / 2 : ℝ) ^ j := by
  have hhalf : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 2)]
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hxj : (j : ℝ) ≤ x / N := (le_div_iff₀ hN).mpr hj
  calc Real.exp (-2 * x / N) ≤ Real.exp (-2 * (j : ℝ)) := by
        apply Real.exp_le_exp.mpr
        rw [show -2 * x / N = -2 * (x / N) by ring]
        linarith
    _ = Real.exp (-2 : ℝ) ^ j := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_left₀ (Real.exp_pos _).le hhalf j

/-- The positive blocks cover precisely the positive half line.
Source: the interval splitting on P0051 page 11. -/
theorem blocks_union {N : ℝ} (hN : 0 < N) : (⋃ j : ℕ, block N j) = Ioi 0 := by
  ext x
  simp only [mem_iUnion, block, mem_inter_iff, mem_Ioi, mem_Ico]
  constructor
  · rintro ⟨j, hx, _, _⟩
    exact hx
  · intro hx
    let j : ℕ := ⌊x / N⌋₊
    have hj : (j : ℝ) ≤ x / N := Nat.floor_le (div_nonneg hx.le hN.le)
    have hj' : x / N < (j : ℝ) + 1 := Nat.lt_floor_add_one (x / N)
    exact ⟨j, hx, (le_div_iff₀ hN).mp hj, (div_lt_iff₀ hN).mp hj'⟩

/-- Distinct positive blocks are disjoint.
Source: the countable interval splitting on P0051 page 11. -/
theorem blocks_disjoint {N : ℝ} (hN : 0 < N) : Pairwise (Disjoint on block N) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi : (i : ℝ) * N ≤ x ∧ x < ((i : ℝ) + 1) * N := hxi.2
  have hj : (j : ℝ) * N ≤ x ∧ x < ((j : ℝ) + 1) * N := hxj.2
  rcases lt_or_gt_of_ne hij with h | h
  · have hr : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    have hm := mul_le_mul_of_nonneg_right hr hN.le
    linarith [hi.2, hj.1]
  · have hr : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    have hm := mul_le_mul_of_nonneg_right hr hN.le
    linarith [hj.2, hi.1]

/-- LEAF. P0051 page 11, exponential integrals are bounded by geometric prefix sums.
The summability premise is explicit, so the right side is a genuine series. -/
theorem exponential_integral_le_prefix_series {N : ℝ} (hN : 0 < N) (f : ℝ → ℝ)
    (hf0 : ∀ x : ℝ, 0 ≤ f x)
    (hloc : ∀ j : ℕ, IntervalIntegrable f volume 0 (((j : ℝ) + 1) * N))
    (hw : IntegrableOn (fun x : ℝ => f x * Real.exp (-2 * x / N)) (Ioi 0))
    (hs : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1) *
      ∫ x in (0 : ℝ)..(((j : ℝ) + 1) * N), f x)) :
    (∫ x : ℝ in Ioi 0, f x * Real.exp (-2 * x / N)) ≤
      2 * ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
        ∫ x in (0 : ℝ)..(((j : ℝ) + 1) * N), f x := by
  have hsub (j : ℕ) : block N j ⊆ Ioc 0 (((j : ℝ) + 1) * N) := by
    intro x hx
    exact ⟨hx.1, hx.2.2.le⟩
  have hmeas (j : ℕ) : MeasurableSet (block N j) := measurableSet_Ioi.inter measurableSet_Ico
  have hb (j : ℕ) :
      (∫ x : ℝ in block N j, f x * Real.exp (-2 * x / N)) ≤
        2 * (1 / 2 : ℝ) ^ (j + 1) *
          ∫ x in (0 : ℝ)..(((j : ℝ) + 1) * N), f x := by
    have hU : IntegrableOn f (block N j) := (hloc j).1.mono_set (hsub j)
    have hW : IntegrableOn (fun x : ℝ => f x * Real.exp (-2 * x / N)) (block N j) :=
      hw.mono_set inter_subset_left
    have hT : 0 ≤ ((j : ℝ) + 1) * N := by positivity
    calc (∫ x : ℝ in block N j, f x * Real.exp (-2 * x / N))
        ≤ ∫ x : ℝ in block N j, (1 / 2 : ℝ) ^ j * f x := by
          apply setIntegral_mono_on hW (hU.const_mul ((1 / 2 : ℝ) ^ j)) (hmeas j)
          intro x hx
          simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left (exp_block_bound hN j hx.2.1) (hf0 x)
      _ = (1 / 2 : ℝ) ^ j * ∫ x : ℝ in block N j, f x := integral_const_mul _ _
      _ ≤ (1 / 2 : ℝ) ^ j * ∫ x : ℝ in Ioc 0 (((j : ℝ) + 1) * N), f x := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact setIntegral_mono_set (hloc j).1 (Eventually.of_forall hf0)
            (Eventually.of_forall fun x hx => hsub j hx)
      _ = 2 * (1 / 2 : ℝ) ^ (j + 1) *
          ∫ x in (0 : ℝ)..(((j : ℝ) + 1) * N), f x := by
          rw [← intervalIntegral.integral_of_le hT, pow_succ]
          ring
  have hsum := hasSum_integral_iUnion (f := fun x : ℝ => f x * Real.exp (-2 * x / N))
    hmeas (blocks_disjoint hN) (by rwa [blocks_union hN])
  rw [blocks_union hN] at hsum
  have hright : HasSum (fun j : ℕ => 2 * (1 / 2 : ℝ) ^ (j + 1) *
      ∫ x in (0 : ℝ)..(((j : ℝ) + 1) * N), f x)
      (2 * ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
        ∫ x in (0 : ℝ)..(((j : ℝ) + 1) * N), f x) := by
    simpa only [mul_assoc] using hs.hasSum.mul_left (2 : ℝ)
  exact hasSum_le hb hsum hright

end LeanLab.GoldbachAverage.GeometricTail124
