/-
BHP1997, pages 51 and 53. Buchstab model shared by the short weights.
Reuse the method of steps construction already on main.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.I2Range

namespace LeanLab.BHP1997.Task308
open Filter Set
open scoped Topology

/-- Pages 51 and 53, the standard Buchstab function in the density integrals.
The construction comes from Wu 2004 Lemma 2.10 through the method of steps.
Its extension below one is zero. This does not construct a sieve weight. -/
theorem buchstab_model_exists :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω := by
  obtain ⟨F, f, ω, hF, hω⟩ := LeanLab.ChenDoubleSieve.Task275.standard_functions
  let w : ℝ → ℝ := fun u => if 1 ≤ u then ω u else 0
  have hw : ∀ u : ℝ, 1 ≤ u → w u = ω u := by
    intro u hu
    simp [w, hu]
  refine ⟨w, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hω.1.congr (fun u hu => hw u hu)
  · intro u hu hu2
    rw [hw u hu]
    exact hω.2.1 u hu hu2
  · intro u hu
    have hd := hω.2.2 u hu
    rw [hw (u - 1) (by linarith)]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < u by linarith)] with v hv
    rw [hw v hv.le]
  · intro u hu
    simp [w, not_le.mpr hu]

end LeanLab.BHP1997.Task308
