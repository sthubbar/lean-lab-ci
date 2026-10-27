/- CODEX task85. AI wrote these concrete hypothesis checks.
These examples verify nonempty cases of the scalar and finite lemmas.
They do not supply the cited analytic inputs. Binary Goldbach is open. -/
import LeanLab.ExceptionalSet.Lu2010FirstDerivative
import LeanLab.ExceptionalSet.HybridShiftBarrier
import LeanLab.ExceptionalSet.Li2000Lemmas
import LeanLab.ExceptionalSet.Decomp1524a
import LeanLab.ExceptionalSet.Decomp1524b
import LeanLab.ExceptionalSet.Decomp1524c
open Finset Real
example : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
  simp [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
example : (5 : ℝ) < 5.000001 := by norm_num
example : ∀ u : ℕ → ℂ,
    ∑ _r ∈ ({0} : Finset ℕ), ‖∑ n ∈ ({0} : Finset ℕ), (1:ℂ)*u n‖^2 ≤
      (1:ℝ) * ∑ n ∈ ({0} : Finset ℕ), ‖u n‖^2 := by simp
example : ∀ r ∈ ({0,1}:Finset ℕ), ∀ s ∈ ({0,1}:Finset ℕ), r ≠ s → (1:ℝ) ≤ |(r:ℝ)-s| := by
  intro r hr s hs hne
  simp only [mem_insert,mem_singleton] at hr hs
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num at *
example : ∀ α ∈ Set.Icc (0:ℝ) 1,
    ((({0}:Finset ℕ).filter (fun _ => α ≤ (1/2:ℝ))).card : ℝ) ≤ (1:ℝ)*2^(1-α) := by
  intro α hα
  have hh : (1:ℝ) ≤ (2:ℝ)^(1-α) := Real.one_le_rpow (by norm_num) (by linarith [hα.2])
  have hc : ((({0}:Finset ℕ).filter (fun _ => α ≤ (1/2:ℝ))).card : ℝ) ≤ 1 := by
    exact_mod_cast (Finset.card_filter_le ({0}:Finset ℕ) (fun _ => α ≤ (1/2:ℝ)))
  linarith
example : (1:ℝ)<4 ∧ 0<(2:ℝ) ∧ 2 ≤ Real.sqrt 4 ∧ (0:ℝ)≤1-(1/2:ℝ) := by norm_num

example : (0:ℝ) < 0.7 ∧ 0.618 < (0.7:ℝ) ∧ (0.7:ℝ) ≤ 1 ∧
    (0:ℝ) ≤ 0 ∧ (0:ℝ) ≤ 1/10^6 := by norm_num
example : Continuous (fun _ : ℝ => (1:ℂ)) ∧
    (∀ x : ℝ, HasDerivAt (fun _ : ℝ => (1:ℂ)) 0 x) ∧
    IntervalIntegrable (fun _ : ℝ => (1:ℂ)) MeasureTheory.volume 0 1 ∧
    IntervalIntegrable (fun _ : ℝ => (0:ℂ)) MeasureTheory.volume 0 1 := by
  exact ⟨continuous_const, fun x => hasDerivAt_const x 1, intervalIntegrable_const, intervalIntegrable_const⟩
example : (1:ℝ) < 2 ∧ (1:ℝ) ≤ 2 ∧ |(1:ℝ)| * (1:ℝ) ≤ (2:ℝ)/2 := by norm_num
example : (1:ℝ)/2 ≤ ‖∑ n ∈ Icc (2+1:ℕ) (2+1), (n:ℂ)^((1:ℂ)*Complex.I)‖ :=
  by simpa using LeanLab.ExceptionalSet.HybridShiftBarrier.dirichlet_norm_lower 2 1 (by norm_num) 1 (by norm_num)

example : ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc (fun x => x^2) (-1) 1‖ ≤
    8*(2:ℝ)^(-(1/2):ℝ) := by
  apply LeanLab.ExceptionalSet.Lu2010FirstDerivative.secondDerivativeEstimate_proved
    (fun x => x^2) (by fun_prop) (-1) 1 2 (by norm_num) (by norm_num)
  left
  intro x hx
  have hd : deriv (fun x : ℝ => x^2) = fun x => 2*x := by ext t; simp
  simp [hd]
example : ‖LeanLab.ExceptionalSet.Lu2010Lemma4.osc (fun x => -(x^2)) (-1) 1‖ ≤
    8*(2:ℝ)^(-(1/2):ℝ) := by
  apply LeanLab.ExceptionalSet.Lu2010FirstDerivative.secondDerivativeEstimate_proved
    (fun x => -(x^2)) (by fun_prop) (-1) 1 2 (by norm_num) (by norm_num)
  right
  intro x hx
  have hd : deriv (fun x : ℝ => -(x^2)) = fun x => -(2*x) := by ext t; simp
  simp [hd]
