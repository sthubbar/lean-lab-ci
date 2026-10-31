import Mathlib

/-!
# U-1475, T3 MOONSHOT: the Cramer-Granville model with explicit correction variance

AI wrote this Lean code. KNOWN mathematics, elementary. Binary Goldbach is OPEN and nothing
here is progress on it.

The route: model the primes by independent events, W-tricked as Granville does, so that at a
fixed even N the unordered pairs {a, N - a} are disjoint and the events "a and N - a both
prime" are independent with probabilities q_a. Then the model chance that N has no
representation is exactly the product of 1 - q_a, which is at most exp of minus the mean,
`prod_one_sub_le_exp`. Over a window of N the second moment method bounds the number of
zeros by the variance over the squared mean, `zero_count_mul_sq_le`, and the only way it
says anything at one N is the pointwise statement `ne_zero_of_sq_dev_lt`, which asks that
the deviation at that N be below the mean: that is the statement to be proved, not a tool.

* `prod_one_sub_le_exp`: for q_i ≤ 1, no lower bound needed, ∏ (1 - q_i) ≤ exp (- ∑ q_i).
* `zero_count_mul_sq_le`: #{x ∈ s : f x = 0} · μ² ≤ ∑_{x ∈ s} (f x - μ)².
* `ne_zero_of_sq_dev_lt`: if ∑_{x ∈ s} (f x - μ)² < μ², then f x ≠ 0 on s.
-/

namespace LeanLab.Routes.U1475

open Finset

/-- Model lower tail at one N: independent disjoint pair events with probabilities `q i`
all fail with probability `∏ (1 - q i) ≤ exp (- ∑ q i)`. -/
theorem prod_one_sub_le_exp {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (h1 : ∀ i ∈ s, q i ≤ 1) :
    ∏ i ∈ s, (1 - q i) ≤ Real.exp (- ∑ i ∈ s, q i) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i hi; linarith [h1 i hi]
  · intro i hi
    have := Real.add_one_le_exp (- q i)
    linarith

/-- Second moment exceptional count: zeros of `f` on `s` are at most the variance about `μ`
divided by `μ²`, written without division. -/
theorem zero_count_mul_sq_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (μ : ℝ) :
    ((s.filter (fun x => f x = 0)).card : ℝ) * μ ^ 2 ≤ ∑ x ∈ s, (f x - μ) ^ 2 := by
  classical
  have hsub : s.filter (fun x => f x = 0) ⊆ s := Finset.filter_subset _ _
  calc ((s.filter (fun x => f x = 0)).card : ℝ) * μ ^ 2
      = ∑ x ∈ s.filter (fun x => f x = 0), (f x - μ) ^ 2 := by
        rw [Finset.sum_congr rfl (g := fun _ => μ ^ 2)]
        · simp
        · intro x hx
          rw [(Finset.mem_filter.mp hx).2]; ring
    _ ≤ ∑ x ∈ s, (f x - μ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

/-- The pointwise form: total squared deviation below `μ²` forces no zero on `s`. At a single
N this is the hypothesis `(r N - μ)² < μ²`, which is binary Goldbach strength at that N. -/
theorem ne_zero_of_sq_dev_lt {ι : Type*} (s : Finset ι) (f : ι → ℝ) (μ : ℝ)
    (h : ∑ x ∈ s, (f x - μ) ^ 2 < μ ^ 2) : ∀ x ∈ s, f x ≠ 0 := by
  classical
  intro x hx hfx
  have hmem : x ∈ s.filter (fun y => f y = 0) := Finset.mem_filter.mpr ⟨hx, hfx⟩
  have hcard : (1 : ℝ) ≤ ((s.filter (fun y => f y = 0)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, hmem⟩
  have := zero_count_mul_sq_le s f μ
  nlinarith [sq_nonneg μ]

/-- Vacuity: the hypotheses of `prod_one_sub_le_exp` hold, two pairs with q = 1/2. -/
example : ∏ _i ∈ (Finset.range 2), (1 - (1 / 2 : ℝ)) ≤
    Real.exp (- ∑ _i ∈ (Finset.range 2), (1 / 2 : ℝ)) :=
  prod_one_sub_le_exp _ _ (fun _ _ => by norm_num)

/-- Vacuity: `ne_zero_of_sq_dev_lt` applies to the true unordered Goldbach counts
R(10) = 2, R(12) = 1, R(14) = 2 with μ = 2, squared deviation 1 < 4. -/
example : ∀ x ∈ ({10, 12, 14} : Finset ℕ),
    (fun n : ℕ => if n = 12 then (1 : ℝ) else 2) x ≠ 0 := by
  apply ne_zero_of_sq_dev_lt _ _ 2
  simp [Finset.sum_insert]
  norm_num

#print axioms prod_one_sub_le_exp
#print axioms zero_count_mul_sq_le
#print axioms ne_zero_of_sq_dev_lt

end LeanLab.Routes.U1475
