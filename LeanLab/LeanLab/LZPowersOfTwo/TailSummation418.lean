/-
Periodic tail summation for P0079 page 10, Section 5.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp293b
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5, the inverse-square series in the displayed chain.
A finite arithmetic-progression tail is bounded by a telescoping reciprocal sum. -/
theorem inverse_square_sum418 (a h : ℝ) (hh : 0 < h) (ha : h ≤ a) (N : ℕ) :
    ∑ n ∈ range N, 1 / (a + (n : ℝ) * h) ^ 2 ≤ 2 / (h * a) := by
  have ha0 : 0 < a := hh.trans_le ha
  have hterm (n : ℕ) : 1 / (a + (n : ℝ) * h) ^ 2 ≤
      (2 / h) * (1 / (a + (n : ℝ) * h) - 1 / (a + ((n + 1 : ℕ) : ℝ) * h)) := by
    have hn : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    have hx : 0 < a + (n : ℝ) * h := by linarith
    have hx' : 0 < a + (n : ℝ) * h + h := by linarith
    have heq : (2 / h) * (1 / (a + (n : ℝ) * h) -
        1 / (a + ((n + 1 : ℕ) : ℝ) * h)) =
        2 / ((a + (n : ℝ) * h) * (a + (n : ℝ) * h + h)) := by
      push_cast
      field_simp
      ring
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hx) (mul_pos hx hx')).mpr
    nlinarith
  calc
    _ ≤ ∑ n ∈ range N, (2 / h) * (1 / (a + (n : ℝ) * h) -
        1 / (a + ((n + 1 : ℕ) : ℝ) * h)) := sum_le_sum (fun n _ => hterm n)
    _ = (2 / h) * (1 / a - 1 / (a + (N : ℝ) * h)) := by
      rw [← mul_sum, sum_range_sub']
      simp
    _ ≤ (2 / h) * (1 / a) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hn : 0 ≤ (N : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
      have : 0 ≤ 1 / (a + (N : ℝ) * h) := by positivity
      linarith
    _ = _ := by ring

/-- P0079 page 10, Section 5, passage from the unit-interval sum to the tail.
Integrable functions with the stated interval bounds obey the same tail bound. -/
theorem integral_tail_of_interval_bounds418 (f : ℝ → ℝ) (hf : Integrable f)
    (a h B : ℝ) (hh : 0 < h) (ha : h ≤ a) (hB : 0 ≤ B)
    (hb : ∀ n : ℕ, (∫ x in (a + (n : ℝ) * h)..(a + ((n + 1 : ℕ) : ℝ) * h), f x) ≤
      B / (a + (n : ℝ) * h) ^ 2) :
    (∫ x in Set.Ioi a, f x) ≤ 2 * B / (h * a) := by
  let u : ℕ → ℝ := fun n => a + (n : ℝ) * h
  have hu : Monotone u := by
    intro i j hij
    change a + (i : ℝ) * h ≤ a + (j : ℝ) * h
    exact add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hh.le) a
  have hunb : ¬ BddAbove (Set.range u) := by
    intro H
    obtain ⟨b, hb⟩ := H
    obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / h)
    have hn' := (div_lt_iff₀ hh).mp hn
    have Hn := hb (Set.mem_range_self n)
    change a + (n : ℝ) * h ≤ b at Hn
    linarith
  have hcover : (⋃ n : ℕ, Set.Ioc (u n) (u (n + 1))) = Set.Ioi a := by
    simpa [u] using iUnion_Ioc_map_succ_eq_Ioi (f := u)
      (fun n => hu (Nat.zero_le n)) hunb
  have hs := hasSum_integral_iUnion (fun n : ℕ => measurableSet_Ioc)
    hu.pairwise_disjoint_on_Ioc_succ hf.integrableOn
  simp only [Order.succ_eq_add_one] at hs
  rw [hcover] at hs
  apply le_of_tendsto' hs.tendsto_sum_nat
  intro N
  calc
    _ ≤ ∑ n ∈ range N, B / (a + (n : ℝ) * h) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hle : u n ≤ u (n + 1) := hu (by omega)
      rw [← intervalIntegral.integral_of_le hle]
      exact hb n
    _ = B * ∑ n ∈ range N, 1 / (a + (n : ℝ) * h) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ B * (2 / (h * a)) := mul_le_mul_of_nonneg_left
      (inverse_square_sum418 a h hh ha N) hB
    _ = _ := by ring

/-- P0079 page 10, Section 5, symmetry of the two trivial tails.
For an even integrable function, the two-sided tail is twice the positive tail. -/
theorem integral_abs_tail_even418 (f : ℝ → ℝ) (hf : Integrable f)
    (he : ∀ x, f (-x) = f x) (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in {x : ℝ | a < |x|}, f x) = 2 * (∫ x in Set.Ioi a, f x) := by
  have hset : {x : ℝ | a < |x|} = Set.Iio (-a) ∪ Set.Ioi a := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs]
    constructor <;> intro h <;> rcases h with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl h
  have hd : Disjoint (Set.Iio (-a)) (Set.Ioi a) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    change x < -a at hx
    change a < x at hx'
    linarith
  rw [hset, setIntegral_union hd measurableSet_Ioi hf.integrableOn hf.integrableOn]
  have hneg := integral_comp_neg_Ioi a f
  simp_rw [he] at hneg
  rw [integral_Iic_eq_integral_Iio] at hneg
  rw [← hneg]
  ring

end LeanLab.LZPowersOfTwo
