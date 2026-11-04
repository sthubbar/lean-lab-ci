import LeanLab.GoldbachAverage.Decomp124
import LeanLab.GoldbachAverage.Sampling124

/-!
Granville 2007, P0098 pages 166 and 167, sampling proof of Proposition 3.1.
The finitely many saturated probabilities make the selector law defined at small primes.
The two analytic sampling estimates remain OPEN.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp287a
open Finset Set MeasureTheory ProbabilityTheory
open Decomp124

/-- The selector probability on P0098 page 166, with saturation at one. -/
def selectorProbability (γ : ℝ) (p : ℕ) : unitInterval :=
  ⟨if Nat.Prime p then
    min 1 (2 * Real.sqrt (Real.log p ^ 3 / γ) / Real.sqrt p) else 0, by
    split_ifs
    · exact ⟨le_min (by norm_num) (by positivity), min_le_left _ _⟩
    · exact ⟨le_rfl, zero_le_one⟩⟩

/-- The independent prime selectors of P0098 page 166. -/
def selectorMeasure (γ : ℝ) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun p => bernoulliMeasure true false (selectorProbability γ p))

/-- Finite joint success probabilities for the independent selectors on P0098 page 166. -/
theorem selector_joint (γ : ℝ) (s : Finset ℕ) :
    selectorMeasure γ {ω | ∀ p ∈ s, ω p = true} =
      ∏ p ∈ s, ENNReal.ofReal (selectorProbability γ p : ℝ) := by
  change Measure.infinitePi _ (Set.pi (s : Set ℕ) (fun _ => {true})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton true)]
  apply Finset.prod_congr rfl
  intro p hp
  rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton true)
    (by simp) (by simp)]
  exact ENNReal.ofReal_coe_nnreal.symm

/-- LEAF. P0098 page 167, the displays for E W x and W x following eq. 3.3.
The PNT estimate and Chernoff concentration give simultaneous sparse growth.
The positive divergent expected count also gives an infinite selected prime set.
A geometric grid and monotonicity extend the eventual bound to every real cutoff. -/
theorem selector_sparse (γ : ℝ) (hγ : 0 < γ) :
    ∀ᵐ ω ∂selectorMeasure γ, (coinSet ω).Infinite ∧ ∃ η : ℝ, 0 < η ∧
      ∀ x : ℝ, 2 ≤ x → (count (coinSet ω) x : ℝ) ≤
        η * Real.sqrt (x * Real.log x) := by
  sorry

/-- LEAF. P0098 page 166 eq. 3.3.
Disjoint off diagonal prime pairs give the power tail bound.
The constant absorbs the finite initial range and the shift of the index by one. -/
theorem selector_failure_bound (γ : ℝ) (hγ : 0 < γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      selectorMeasure γ {ω | n ∈ richEven γ ∧
        ¬ ∃ p ∈ coinSet ω, ∃ q ∈ coinSet ω, p + q = n} ≤
      ENNReal.ofReal (K * ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2)) := by
  sorry

/-- P0098 page 166, the expectation display after eq. 3.3.
CONDITIONAL ON selector_failure_bound. The summation step reuses Sampling124. -/
theorem selector_misses (γ : ℝ) (hγ : 0 < γ) :
    (∑' n : ℕ, selectorMeasure γ {ω | n ∈ richEven γ ∧
      ¬ ∃ p ∈ coinSet ω, ∃ q ∈ coinSet ω, p + q = n}) ≠ ⊤ := by
  obtain ⟨K, _, hK⟩ := selector_failure_bound γ hγ
  exact Sampling124.failure_mass_finite _ _ K hK

/-- The exact random_model statement assembled from the two smaller sampling leaves.
CONDITIONAL ON selector_sparse and selector_misses. -/
theorem random_model_assembled (γ : ℝ) (hγ : 0 < γ) :
    ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      (∀ᵐ ω ∂μ, (coinSet ω).Infinite ∧ ∃ η : ℝ, 0 < η ∧
        ∀ x : ℝ, 2 ≤ x → (count (coinSet ω) x : ℝ) ≤
          η * Real.sqrt (x * Real.log x)) ∧
      (∑' n : ℕ, μ {ω | n ∈ richEven γ ∧
        ¬ ∃ p ∈ coinSet ω, ∃ q ∈ coinSet ω, p + q = n}) ≠ ⊤ := by
  refine ⟨selectorMeasure γ, ?_, selector_sparse γ hγ, selector_misses γ hγ⟩
  unfold selectorMeasure
  infer_instance

example : type_of% random_model = type_of% random_model_assembled := rfl

end LeanLab.GoldbachAverage.Decomp287a
