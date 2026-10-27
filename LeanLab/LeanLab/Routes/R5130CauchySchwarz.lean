/-
R-5130, T3 MOONSHOT route: the Cauchy-Schwarz density route of Riesel-Vaughan 1983, P0032.
`N ≥ (Σ R(n) a(n))² / Σ (R(n) a(n))²` for any weights `a`, and the 3/4 loss a linearly growing
count suffers without normalisation: `(Σ_{n ≤ X} n)² = (3(X+1)/(2(2X+1))) X Σ_{n ≤ X} n²`.
AI-written Lean code, Claude, 2026-10-20, run 20261020T0316Z-cloud33. Checked only by the
Lean kernel. Binary Goldbach is OPEN; this route reaches almost all even numbers at best.
-/
import Mathlib

open Finset

namespace LeanLab.Routes.R5130

/-- Weighted Cauchy-Schwarz support bound: if `f` vanishes off `S ⊆ T`, then
`(Σ_T f)² ≤ #S · Σ_T f²`; with `f = R·a`, `#S` is the number of represented `n`. -/
theorem support_ge {ι : Type*} [DecidableEq ι] (T S : Finset ι) (hST : S ⊆ T) (f : ι → ℝ)
    (hf : ∀ i ∈ T, i ∉ S → f i = 0) :
    (∑ i ∈ T, f i) ^ 2 ≤ #S * ∑ i ∈ T, f i ^ 2 := by
  have h1 : ∑ i ∈ T, f i = ∑ i ∈ S, f i := by
    rw [← sum_subset hST (fun i hi hn => hf i hi hn)]
  have h2 : ∑ i ∈ S, f i ^ 2 ≤ ∑ i ∈ T, f i ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => sq_nonneg _)
  rw [h1]
  calc (∑ i ∈ S, f i) ^ 2 ≤ #S * ∑ i ∈ S, f i ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ #S * ∑ i ∈ T, f i ^ 2 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)

lemma sum_id (X : ℕ) : ∑ i ∈ range (X + 1), (i : ℝ) = X * (X + 1) / 2 := by
  induction X with
  | zero => simp
  | succ X ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_sq (X : ℕ) : ∑ i ∈ range (X + 1), (i : ℝ) ^ 2 = X * (X + 1) * (2 * X + 1) / 6 := by
  induction X with
  | zero => simp
  | succ X ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The size loss: for the count `R(n) = n` on `0 ≤ n ≤ X` Cauchy-Schwarz returns
`3(X+1)/(2(2X+1))` of the `X` points, which tends to 3/4. This is the limit of the lab's
numerical CS ratio for the weighted Goldbach count over all `n ≤ X`, 0.80, 0.79, 0.787 at
`X = 10^5, 10^6, 10^7`, and why Riesel-Vaughan cut `(y, x]` into `K = 200` short blocks. -/
theorem cs_linear_ratio (X : ℕ) :
    (∑ i ∈ range (X + 1), (i : ℝ)) ^ 2 =
      3 * (X + 1) / (2 * (2 * X + 1)) * (X * ∑ i ∈ range (X + 1), (i : ℝ) ^ 2) := by
  rw [sum_id, sum_sq]
  have : (0 : ℝ) < 2 * X + 1 := by positivity
  field_simp
  ring

/-- The ratio tends to 3/4 from above: `3(X+1)/(2(2X+1)) - 3/4 = 3/(4(2X+1))`. -/
theorem cs_linear_ratio_sub (X : ℕ) :
    3 * ((X : ℝ) + 1) / (2 * (2 * X + 1)) - 3 / 4 = 3 / (4 * (2 * X + 1)) := by
  have : (0 : ℝ) < 2 * X + 1 := by positivity
  field_simp
  ring

/-- The parity ceiling in its simplest form: if the only bound on `Σ f²` is `κ` times the
truth `(Σ f)²/M`, Cauchy-Schwarz gives at most `M/κ` represented points. With a prime pair
upper bound sieve `κ ≥ 2` by the parity phenomenon, so at most half of the even numbers. -/
theorem cs_ceiling (s q M κ : ℝ) (hM : 0 < M) (hκ : 0 < κ) (hs : s ≠ 0)
    (hq : q = κ * s ^ 2 / M) : s ^ 2 / q = M / κ := by
  rw [hq]
  field_simp

end LeanLab.Routes.R5130
