import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Decomp587j

/-!
Concrete analytic instances for the row two Buchstab certificates.
Source: https://arxiv.org/abs/0705.1652, Lemma 2.10 page 9 and page 26.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory Filter
namespace LeanLab.ChenDoubleSieve.Task660
open Wu04Functional

/-- A Buchstab function exists with the zero extension used by Wu's sieve integrals. -/
theorem exists_zero_extended_buchstab :
    ∃ ω : ℝ → ℝ, IsBuchstab ω ∧ ZeroBelowOne ω := by
  obtain ⟨F, f, ω, _, hω⟩ := Task275.standard_functions
  let W : ℝ → ℝ := fun u => if 1 ≤ u then ω u else 0
  have hW (u : ℝ) (hu : 1 ≤ u) : W u = ω u := by simp [W, hu]
  refine ⟨W, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hω.1.congr (fun u hu => hW u hu)
  · intro u hu hu2
    rw [hW u hu]
    exact hω.2.1 u hu hu2
  · intro u hu
    rw [hW (u - 1) (by linarith)]
    apply (hω.2.2 u hu).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < u by linarith)] with v hv
    rw [hW v hv.le]
  · intro u hu
    simp [W, not_le.mpr hu]

/-- The four row two compact bounds have a common concrete analytic instance at phi two. -/
theorem row_two_bounds_instance :
    ∃ ω : ℝ → ℝ, IsBuchstab ω ∧ ZeroBelowOne ω ∧
      buchstabIntegral ω 1 (fun j => (Task587.r1j13_lo j : ℝ))
        (fun j => (Task587.r1j13_hi j : ℝ)) 2 ≤ (20031169 / 1000000000 : ℝ) ∧
      buchstabIntegral ω 1 (fun j => (Task587.r1j14_lo j : ℝ))
        (fun j => (Task587.r1j14_hi j : ℝ)) 2 ≤ (9167311 / 1000000000 : ℝ) ∧
      buchstabIntegral ω 1 (fun j => (Task587.r1j15_lo j : ℝ))
        (fun j => (Task587.r1j15_hi j : ℝ)) 2 ≤ (2887983 / 1000000000 : ℝ) ∧
      buchstabIntegral ω 2 (fun j => (Task587.r1j16_lo j : ℝ))
        (fun j => (Task587.r1j16_hi j : ℝ)) 2 ≤ (35393 / 500000000 : ℝ) := by
  obtain ⟨ω, hω, hz⟩ := exists_zero_extended_buchstab
  exact ⟨ω, hω, hz,
    Task587.r1j13_short hω hz le_rfl (by norm_num),
    Task587.r1j14_short hω hz le_rfl (by norm_num),
    Task587.r1j15_short hω hz le_rfl (by norm_num),
    Task587.r1j16_short hω hz le_rfl (by norm_num)⟩

end LeanLab.ChenDoubleSieve.Task660
#print axioms LeanLab.ChenDoubleSieve.Task660.exists_zero_extended_buchstab
#print axioms LeanLab.ChenDoubleSieve.Task660.row_two_bounds_instance
