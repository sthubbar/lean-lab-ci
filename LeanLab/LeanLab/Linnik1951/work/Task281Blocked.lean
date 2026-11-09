import Mathlib

#find DirichletCharacter.LFunction lower bound
#find DirichletCharacter.LFunction norm log

example {f : ℝ → ℂ} (hf : Continuous f) (hnz : ∀ x, f x ≠ 0) :
    Continuous (fun x => Complex.log (f x)) := by
  apply Continuous.clog
  · exact hf
  · intro x
    exact hnz x

example {z M : ℝ} (hz : 0 < z) (hM : 0 < M) (h : z ≤ M) :
    |Real.log z| ≤ Real.log M := by
  rw [abs_le]
  constructor
  · linarith [Real.log_le_log hz h]
  · linarith [Real.log_le_log hz h]
