/-
Jia 1996 page 260, Lemma 19.
Source https://doi.org/10.4064/aa-77-3-207-287.
The bounded rough weight input is stated separately from its region specializations.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Source565

namespace LeanLab.Languasco2004.Decomp565d
open Finset Real Decomp279a Decomp316a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 260 Lemma 19: count prime cofactors in the actual correlation or the model interval. -/
def cofactorCount (model : Bool) (N Y : ℝ) (n m : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    if model then Y < ((m * p : ℕ) : ℝ) ∧ ((m * p : ℕ) : ℝ) ≤ 2 * Y
    else m * p ≤ n ∧ ((m * p : ℕ) : ℝ) ≤ 2 * Y ∧ (n - m * p).Prime ∧
      N - Y < ((n - m * p : ℕ) : ℝ) ∧ ((n - m * p : ℕ) : ℝ) ≤ N)).card

/-- Page 260 Lemma 19: a nonnegative dyadic weight sum of the prime cofactor counts. -/
def weightedCofactors (model : Bool) (N Y M : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ (range (n + 1)).filter (fun m : ℕ => M < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M),
    a m * (cofactorCount model N Y n m : ℝ)

/-- Page 260 Lemma 19: nonnegative weights give nonnegative cofactor sums. -/
lemma weightedCofactors_nonneg (model : Bool) (N Y M : ℝ) (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m) :
    0 ≤ weightedCofactors model N Y M n a := by
  exact sum_nonneg fun m _ => mul_nonneg (ha m) (Nat.cast_nonneg _)

/-- Page 260 Lemma 19: the absolute error allowance makes the tolerance positive. -/
lemma rough_tolerance_pos (N Y M B : ℝ) (n : ℕ) (a : ℕ → ℝ)
    (hN : 1 < N) (hY : 0 < Y) (ha : ∀ m, 0 ≤ a m) :
    0 < singular n * weightedCofactors true N Y M n a / log N ^ (2 : ℕ) +
      Y / log N ^ B := by
  exact add_pos_of_nonneg_of_pos
    (div_nonneg (mul_nonneg (singular_nonneg n)
      (weightedCofactors_nonneg true N Y M n a ha)) (sq_nonneg _))
    (div_pos hY (Real.rpow_pos_of_pos (Real.log_pos hN) B))

/-- Page 260 Lemma 19: increasing the positive error constant shrinks the exceptional set. -/
lemma rough_exceptional_antitone (N ε M B D₁ D₂ : ℝ) (a : ℕ → ℝ)
    (hN : 1 < N) (ha : ∀ m, 0 ≤ a m) (hD : D₁ ≤ D₂) :
    ((window N ε).filter (fun n =>
      D₂ * (singular n * weightedCofactors true N (localization N ε) M n a /
          log N ^ (2 : ℕ) + localization N ε / log N ^ B) <
        |weightedCofactors false N (localization N ε) M n a -
          singular n / log N * weightedCofactors true N (localization N ε) M n a|)).card ≤
    ((window N ε).filter (fun n =>
      D₁ * (singular n * weightedCofactors true N (localization N ε) M n a /
          log N ^ (2 : ℕ) + localization N ε / log N ^ B) <
        |weightedCofactors false N (localization N ε) M n a -
          singular n / log N * weightedCofactors true N (localization N ε) M n a|)).card := by
  apply card_le_card
  intro n hn
  obtain ⟨hn, hbad⟩ := mem_filter.mp hn
  refine mem_filter.mpr ⟨hn, lt_of_le_of_lt ?_ hbad⟩
  exact mul_le_mul_of_nonneg_right hD
    (rough_tolerance_pos N (localization N ε) M B n a hN
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hN) _) ha).le

/-- Page 260 Lemma 19: the lower endpoint is an admissible dyadic scale for small epsilon. -/
lemma rough_scale_bounds (N ε : ℝ) (hN : 1 ≤ N) (hε : 0 < ε)
    (hsmall : ε ≤ (16 / 135 : ℝ) ^ 3) :
    (localization N ε) ^ (119 / 135 : ℝ) ≤
      (localization N ε) ^ (1 - delta ε) := by
  have hY : 1 ≤ localization N ε :=
    Real.one_le_rpow hN (by linarith)
  exact Real.rpow_le_rpow_of_exponent_le hY
    (by have := Source565.delta_cutoff ε hε hsmall; linarith)

/-- LEAF. Jia page 260, Lemma 19, unnumbered displayed asymptotic formula.
The written proof invokes Lemmas 5 and 18. The relative error of order
one divided by log N and the absolute error of order Y divided by log N to B
are both retained, with one positive constant bounding their two constants.
The weight is bounded by one and vanishes on integers with a prime factor below Y to delta.
This input underlies displays 59 and 63 on pages 283 and 284. -/
theorem lemma19_rough_input :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ M : ℝ → ℝ, ∀ a : ℝ → ℕ → ℝ,
      (∀ N : ℝ, 2 ≤ N →
        (localization N ε) ^ (119 / 135 : ℝ) ≤ M N ∧
          M N ≤ (localization N ε) ^ (1 - delta ε)) →
      (∀ N : ℝ, ∀ m : ℕ, 0 ≤ a N m ∧ a N m ≤ 1) →
      (∀ N : ℝ, 2 ≤ N → ∀ m p : ℕ, p.Prime → p ∣ m →
        (p : ℝ) < (localization N ε) ^ delta ε → a N m = 0) →
    ∃ C D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        D * (singular n * weightedCofactors true N (localization N ε) (M N) n (a N) /
            log N ^ (2 : ℕ) + localization N ε / log N ^ B) <
          |weightedCofactors false N (localization N ε) (M N) n (a N) -
            singular n / log N * weightedCofactors true N (localization N ε) (M N) n (a N)|)).card : ℝ) ≤
      C * windowLength N ε / log N ^ B := by
  intro ε₀ hε₀ ε B hε hε₀' hB M a hM ha hrough
  exact?

/-- Page 260: zero weights satisfy the rough support condition and give both counts zero. -/
theorem rough_zero_weights (N Y M : ℝ) (n : ℕ) :
    weightedCofactors false N Y M n (fun _ => 0) = 0 ∧
      weightedCofactors true N Y M n (fun _ => 0) = 0 := by
  simp [weightedCofactors]

#print axioms lemma19_rough_input
#print axioms rough_zero_weights
#print axioms weightedCofactors_nonneg
#print axioms rough_tolerance_pos
#print axioms rough_exceptional_antitone
#print axioms rough_scale_bounds
end
end LeanLab.Languasco2004.Decomp565d
