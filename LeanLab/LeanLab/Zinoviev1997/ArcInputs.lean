/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Separate inputs for Lemmas 2.1 and 3.2, pages 343 and 352 to 356.
Lemma 3.3 is supplied by ModelIntegral.lean without GRH.
The singular series lower bound on page 357 is a separate cited input.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ModelIntegral

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology LeanLab.CircleOrth MeasureTheory

/-- Q from page 343. -/
noncomputable def arcCutoff (N : ℕ) : ℕ := ⌊1.1 * Real.log N ^ 2⌋₊

/-- The major arc radius delta_N q from page 343. -/
noncomputable def arcRadius (N q : ℕ) : ℝ := 2 * Real.log N / (Nat.totient q * N)

/-- The reflected periodic major arcs, restricted to a full period by the integrals. -/
noncomputable def majorArcs (N : ℕ) : Set ℝ :=
  ⋃ q ∈ Finset.Icc 1 (arcCutoff N), ⋃ a ∈ Finset.range q,
    ⋃ (_ : Nat.Coprime a q), ⋃ k : ℤ,
      {α : ℝ | |α + (a : ℝ) / q - k| ≤ arcRadius N q}

theorem measurableSet_majorArcs (N : ℕ) : MeasurableSet (majorArcs N) := by
  unfold majorArcs
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun k => ?_
  exact (isClosed_le (show Continuous (fun α : ℝ => |α + (a : ℝ) / q - k|) by
    fun_prop) continuous_const).measurableSet

/-- Lemma 2.1, page 343, in the reflected convention. This remains a cited GRH input. -/
def Lemma21Input (N : ℕ) : Prop :=
  ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ majorArcs N,
    ‖SZ N α‖ ≤ 0.18 * N / Real.log N

/-- Lemma 3.2 with the 0.04 error proved on page 356. This remains a cited GRH input.
The real sigma is the singular series specified in that lemma. -/
def Lemma32Input (N : ℕ) (σ : ℝ) : Prop :=
  ‖(∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs N,
      SZ N α ^ 3 * ee (-((N : ℤ) * α))) - (σ : ℂ) * modelIntegral N‖ ≤
    0.04 * (N : ℝ) ^ 2

/-- Page 357 cites the singular series bound for odd N. No GRH enters this bound. -/
def SingularSeriesLower (σ : ℝ) : Prop := 12 / Real.pi ^ 2 < σ

/-- The decimal comparison in the proof of Theorem 3.4 is elementary. -/
theorem singularSeries_decimal {σ : ℝ} (hσ : SingularSeriesLower σ) : 1.21 < σ := by
  have hp : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  have hpi := Real.pi_lt_d4
  have hn : 1.21 < 12 / Real.pi ^ 2 := by
    rw [lt_div_iff₀ hp]
    nlinarith [Real.pi_pos]
  exact hn.trans hσ

/-- ArcInput follows from the two cited arc bounds and the separate singular series bound.
There is no cited Lemma 3.3 hypothesis. -/
theorem arcInput_of_lemmas (N : ℕ) (hN : 8 ≤ N) (σ : ℝ)
    (h21 : Lemma21Input N) (h32 : Lemma32Input N σ)
    (hσ : SingularSeriesLower σ) : ArcInput N := by
  obtain ⟨θ, hθ, hmodel⟩ := modelIntegral_theta N hN
  refine ⟨majorArcs N, measurableSet_majorArcs N, h21, σ, θ,
    singularSeries_decimal hσ, hθ, ?_⟩
  have heq : (σ : ℂ) * modelIntegral N =
      ((σ / Real.exp 1 * ((N : ℝ) ^ 2 / 2 + 8 * θ * N) : ℝ) : ℂ) := by
    rw [hmodel]
    push_cast
    ring
  simpa only [Lemma32Input, heq] using h32

/-- Theorem 3.4, CONDITIONAL ON Lemma21Input, Lemma32Input and SingularSeriesLower. -/
theorem zinoviev_of_lemmas (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) (σ : ℝ)
    (h21 : Lemma21Input N) (h32 : Lemma32Input N σ)
    (hσ : SingularSeriesLower σ) : IsTernarySum N := by
  apply zinoviev_of_arcs N hN
  have hn : 8 ≤ N := by
    have : (8 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  exact arcInput_of_lemmas N hn σ h21 h32 hσ

end LeanLab.Zinoviev1997
