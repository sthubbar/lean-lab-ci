import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.I2Range

/-!
Domain extension checks for the lab Buchstab predicate.
Source: Wu 2004 Lemma 2.10 page 9 and the explicit I2Range extension convention.
These are derived model facts. They do not assert a paper error.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set Filter
open scoped Topology
namespace LeanLab.ChenDoubleSieve.Task659Vacuity
open Wu04Functional

/-- Changing values below one to a fixed constant preserves the defining predicate. -/
theorem extend_below_one_isBuchstab {ω : ℝ → ℝ} (hω : IsBuchstab ω) (c : ℝ) :
    IsBuchstab (fun u => if 1 ≤ u then ω u else c) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (continuousOn_congr ?_).mpr hω.1
    intro u hu
    change (1 : ℝ) ≤ u at hu
    exact if_pos hu
  · intro u hu hu2
    change (if 1 ≤ u then ω u else c) = 1 / u
    rw [if_pos hu]
    exact hω.2.1 u hu hu2
  · intro u hu
    have hu1 : (1 : ℝ) ≤ u - 1 := by linarith
    change HasDerivAt (fun v : ℝ => v * (if 1 ≤ v then ω v else c))
      (if 1 ≤ u - 1 then ω (u - 1) else c) u
    rw [if_pos hu1]
    apply (hω.2.2 u hu).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (show (1 : ℝ) < u by linarith)] with v hv
    simp only [if_pos hv.le]

/-- The two hypotheses of every requested short leaf hold for a real function. -/
theorem exists_buchstab_zeroBelowOne :
    ∃ ω : ℝ → ℝ, IsBuchstab ω ∧ ZeroBelowOne ω := by
  obtain ⟨_, _, ω, _, hω⟩ := Task275.standard_functions
  refine ⟨fun u => if 1 ≤ u then ω u else 0, extend_below_one_isBuchstab hω 0, ?_⟩
  intro u hu
  exact if_neg (not_le.mpr hu)

/-- The zero extension convention is independent of the defining predicate. -/
theorem exists_isBuchstab_not_zeroBelowOne :
    ∃ ω : ℝ → ℝ, IsBuchstab ω ∧ ¬ ZeroBelowOne ω := by
  obtain ⟨_, _, ω, _, hω⟩ := Task275.standard_functions
  refine ⟨fun u => if 1 ≤ u then ω u else 1, extend_below_one_isBuchstab hω 1, ?_⟩
  intro hz
  have hz0 := hz 0 (by norm_num)
  norm_num at hz0

end LeanLab.ChenDoubleSieve.Task659Vacuity
#print axioms LeanLab.ChenDoubleSieve.Task659Vacuity.extend_below_one_isBuchstab
#print axioms LeanLab.ChenDoubleSieve.Task659Vacuity.exists_buchstab_zeroBelowOne
#print axioms LeanLab.ChenDoubleSieve.Task659Vacuity.exists_isBuchstab_not_zeroBelowOne
