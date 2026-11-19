/-
Auxiliary checks for Wu 2004.
The zero extension supplies a concrete instance for the compact certificates.
The positive matrix entries rule out the zero lower bound method.
AI wrote the Lean code. Binary Goldbach is open.
-/

import LeanLab.ChenDoubleSieve.I2Range
import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Table1Algebra

open Set Filter
open scoped Topology Classical
open LeanLab.ChenDoubleSieve.Wu04Functional

namespace LeanLab.ChenDoubleSieve.Task658

theorem buchstab_zero_extension {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    IsBuchstab ((Ici 1).indicator ω) ∧ ZeroBelowOne ((Ici 1).indicator ω) := by
  constructor
  · refine ⟨hω.1.congr ?_, ?_, ?_⟩
    · intro u hu
      exact indicator_of_mem hu ω
    · intro u hu1 hu2
      rw [indicator_of_mem (show u ∈ Ici (1 : ℝ) from hu1) ω]
      exact hω.2.1 u hu1 hu2
    · intro u hu
      have he : (fun v => v * (Ici 1).indicator ω v) =ᶠ[𝓝 u] (fun v => v * ω v) := by
        filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) < u by linarith)] with v hv
        have hv1 : (1 : ℝ) < v := hv
        rw [indicator_of_mem (show v ∈ Ici (1 : ℝ) from hv1.le) ω]
      have hd := (hω.2.2 u hu).congr_of_eventuallyEq he
      simpa only [indicator_of_mem (show u - 1 ∈ Ici (1 : ℝ) by change 1 ≤ u - 1; linarith) ω] using hd
  · intro u hu
    exact indicator_of_notMem (show u ∉ Ici (1 : ℝ) from not_le.mpr hu) ω

theorem zero_extended_buchstab_exists :
    ∃ ω : ℝ → ℝ, IsBuchstab ω ∧ ZeroBelowOne ω := by
  obtain ⟨F, f, ω, hF, hω⟩ := LeanLab.ChenDoubleSieve.Task275.standard_functions
  exact ⟨(Ici 1).indicator ω, buchstab_zero_extension hω⟩

open LeanLab.ChenDoubleSieve.Wu04Table

theorem candidate_zero_bound_insufficient :
    ∀ i j : Fin 9, ¬ (candidateMatrixQ i j : ℝ) ≤ 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [candidateMatrixQ]

end LeanLab.ChenDoubleSieve.Task658
