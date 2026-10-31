/-
AI wrote this Lean code for CODEX task58.
Quadrature infrastructure for P0039 equation 3.9 and pages 66 to 67.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.U1435C0

open Real intervalIntegral MeasureTheory Set Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- Endpoint bounds for one increasing cell. -/
theorem monotone_cell {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hm : MonotoneOn f (Icc a b)) :
    (b - a) * f a ≤ ∫ x in a..b, f x ∧
      (∫ x in a..b, f x) ≤ (b - a) * f b := by
  constructor
  · have h := integral_mono_on hab (intervalIntegrable_const) hf
      (fun x hx => hm ⟨le_rfl, hab⟩ hx hx.1)
    simpa using h
  · have h := integral_mono_on hab hf (intervalIntegrable_const)
      (fun x hx => hm hx ⟨hab, le_rfl⟩ hx.2)
    simpa using h

/-- Endpoint bounds for one decreasing cell. -/
theorem antitone_cell {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hm : AntitoneOn f (Icc a b)) :
    (b - a) * f b ≤ ∫ x in a..b, f x ∧
      (∫ x in a..b, f x) ≤ (b - a) * f a := by
  constructor
  · have h := integral_mono_on hab (intervalIntegrable_const) hf
      (fun x hx => hm hx ⟨hab, le_rfl⟩ hx.2)
    simpa using h
  · have h := integral_mono_on hab hf (intervalIntegrable_const)
      (fun x hx => hm ⟨le_rfl, hab⟩ hx hx.1)
    simpa using h

/-- Darboux bounds with an explicit increasing or decreasing choice on every cell. -/
theorem riemann_bounds {f : ℝ → ℝ} {a : ℕ → ℝ} {n : ℕ} {inc : ℕ → Bool}
    (ha : ∀ k < n, a k ≤ a (k + 1))
    (hf : ∀ k < n, IntervalIntegrable f volume (a k) (a (k + 1)))
    (hm : ∀ k < n, if inc k then MonotoneOn f (Icc (a k) (a (k + 1)))
      else AntitoneOn f (Icc (a k) (a (k + 1)))) :
    (∑ k ∈ range n, (a (k + 1) - a k) *
      (if inc k then f (a k) else f (a (k + 1)))) ≤ ∫ x in a 0..a n, f x ∧
    (∫ x in a 0..a n, f x) ≤ ∑ k ∈ range n, (a (k + 1) - a k) *
      (if inc k then f (a (k + 1)) else f (a k)) := by
  rw [← sum_integral_adjacent_intervals hf]
  constructor <;> apply sum_le_sum <;> intro k hk
  · have hk' := mem_range.mp hk
    have hmk := hm k hk'
    cases h : inc k <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hmk ⊢
    · exact (antitone_cell (ha k hk') (hf k hk') hmk).1
    · exact (monotone_cell (ha k hk') (hf k hk') hmk).1
  · have hk' := mem_range.mp hk
    have hmk := hm k hk'
    cases h : inc k <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hmk ⊢
    · exact (antitone_cell (ha k hk') (hf k hk') hmk).2
    · exact (monotone_cell (ha k hk') (hf k hk') hmk).2

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.monotone_cell
#print axioms LeanLab.ChenPrimeExceptional.Task58.antitone_cell
#print axioms LeanLab.ChenPrimeExceptional.Task58.riemann_bounds
