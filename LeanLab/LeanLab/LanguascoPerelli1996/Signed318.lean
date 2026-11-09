import LeanLab.LanguascoPerelli1996.Interpolation318
import LeanLab.LanguascoPerelli1996.Partial318

/-!
Derived signed frequency audit for P0071 page 355 display 13.
This example is not a Dirichlet zero counterexample or a paper error.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Signed318
open Complex Real MeasureTheory Interpolation318

/-- Page 355 display 13, derived exact two frequency test of the kernel calculation.
Coefficients one and minus one at frequencies minus one and one have mass one.
Multiplying each coefficient by its frequency raises the mass to three. -/
theorem signed_mass_values :
    mass Finset.univ (fun b : Bool => if b then (-1 : ℂ) else 1)
      (fun b : Bool => if b then (1 : ℝ) else -1) = 1 ∧
    mass Finset.univ (fun _ : Bool => (-1 : ℂ))
      (fun b : Bool => if b then (1 : ℝ) else -1) = 3 := by
  have h0 := (FiniteEnergy108.finite_energy_identity Finset.univ
    (fun b : Bool => if b then (-1 : ℂ) else 1)
    (fun b : Bool => if b then (1 : ℝ) else -1)).2
  have h1 := (FiniteEnergy108.finite_energy_identity Finset.univ
    (fun _ : Bool => (-1 : ℂ))
    (fun b : Bool => if b then (1 : ℝ) else -1)).2
  have h0r := congrArg Complex.re h0
  have h1r := congrArg Complex.re h1
  change mass _ _ _ = _ at h0r h1r
  norm_num [w, Fintype.sum_bool] at h0r h1r
  exact ⟨h0r, h1r⟩

/-- Page 355 display 13, derived concrete witness for the prefix mass premise.
The signed example has every symmetric prefix mass at most one. -/
theorem signed_prefix_mass_le (u : ℝ) :
    mass Finset.univ
      (fun b : Bool => if |if b then (1 : ℝ) else -1| ≤ u then
        (if b then (-1 : ℂ) else 1) else 0)
      (fun b : Bool => if b then (1 : ℝ) else -1) ≤ 1 := by
  by_cases hu : 1 ≤ u
  · have he := Partial318.mass_congr Finset.univ
      (fun b : Bool => if |if b then (1 : ℝ) else -1| ≤ u then
        (if b then (-1 : ℂ) else 1) else 0)
      (fun b : Bool => if b then (-1 : ℂ) else 1)
      (fun b : Bool => if b then (1 : ℝ) else -1) (by
        intro b hb
        cases b <;> simp [hu])
    rw [he, signed_mass_values.1]
  · have he := Partial318.mass_congr Finset.univ
      (fun b : Bool => if |if b then (1 : ℝ) else -1| ≤ u then
        (if b then (-1 : ℂ) else 1) else 0)
      (fun _ : Bool => (0 : ℂ))
      (fun b : Bool => if b then (1 : ℝ) else -1) (by
        intro b hb
        cases b <;> simp [hu])
    rw [he]
    simp [mass]

/-- Page 355 display 13, derived negative result for the naive signed contraction.
Even uniform symmetric prefix control does not make multiplication by gamma
contractive when all absolute frequencies are at most one. -/
theorem signed_contraction_false :
    ¬ ∀ (c : Bool → ℂ) (γ : Bool → ℝ), (∀ b, |γ b| ≤ 1) →
      (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        mass Finset.univ (fun b => if |γ b| ≤ u then c b else 0) γ ≤ 1) →
          mass Finset.univ (fun b => (γ b : ℂ) * c b) γ ≤ 1 := by
  intro h
  let c : Bool → ℂ := fun b => if b then -1 else 1
  let γ : Bool → ℝ := fun b => if b then 1 else -1
  have hh := h c γ (by intro b; cases b <;> norm_num [γ])
    (fun u _ _ => signed_prefix_mass_le u)
  have he : mass Finset.univ (fun b => (γ b : ℂ) * c b) γ =
      mass Finset.univ (fun _ : Bool => (-1 : ℂ)) γ := by
    apply Partial318.mass_congr
    intro b hb
    cases b <;> norm_num [c, γ]
  have hv : mass Finset.univ (fun _ : Bool => (-1 : ℂ)) γ = 3 := signed_mass_values.2
  rw [he, hv] at hh
  norm_num at hh

end LeanLab.LanguascoPerelli1996.Signed318

#print axioms LeanLab.LanguascoPerelli1996.Signed318.signed_mass_values
#print axioms LeanLab.LanguascoPerelli1996.Signed318.signed_prefix_mass_le
#print axioms LeanLab.LanguascoPerelli1996.Signed318.signed_contraction_false
