import LeanLab.ChenDoubleSieve.Burst9Top
import LeanLab.ChenDoubleSieve.Decomp587l

/-!
Concrete hypothesis instances for the compact Buchstab certificates.
Wu 2004 Lemma 2.10 page 9 and Lemma 5.2 page 26.
The endpoints use Table 1 row 1 page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Set Real MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task661
open Wu04Functional Task587

/-- The five compact certificates have a common function and phi instance. -/
theorem short_hypotheses_nonempty :
    ∃ ω : ℝ → ℝ, IsBuchstab ω ∧ ZeroBelowOne ω ∧
      (2 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 7 / 2 := by
  obtain ⟨F, f, ω, hF, hω⟩ := Task275.standard_functions
  exact ⟨Burst9Top.zeroExt ω, Burst9Top.zeroExt_isBuchstab hω,
    Burst9Top.zeroExt_zero ω, le_rfl, by norm_num⟩

/-- The rational lower corners belong to all five ordered domains. -/
theorem lower_corners_mem :
    (fun j => (r0j14_lo j : ℝ)) ∈ domain (fun j => (r0j14_lo j : ℝ)) (fun j => (r0j14_hi j : ℝ)) ∧
    (fun j => (r0j15_lo j : ℝ)) ∈ domain (fun j => (r0j15_lo j : ℝ)) (fun j => (r0j15_hi j : ℝ)) ∧
    (fun j => (r0j16_lo j : ℝ)) ∈ domain (fun j => (r0j16_lo j : ℝ)) (fun j => (r0j16_hi j : ℝ)) ∧
    (fun j => (r0j17_lo j : ℝ)) ∈ domain (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) ∧
    (fun j => (r0j19_lo j : ℝ)) ∈ domain (fun j => (r0j19_lo j : ℝ)) (fun j => (r0j19_hi j : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num [r0j14_lo] at *
  · intro j
    fin_cases j <;> norm_num [r0j14_lo, r0j14_hi]
  · intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num [r0j15_lo] at *
  · intro j
    fin_cases j <;> norm_num [r0j15_lo, r0j15_hi]
  · intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num [r0j16_lo] at *
  · intro j
    fin_cases j <;> norm_num [r0j16_lo, r0j16_hi]

  · intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num [r0j17_lo] at *
  · intro j
    fin_cases j <;> norm_num [r0j17_lo, r0j17_hi]

  · intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num [r0j19_lo] at *
  · intro j
    fin_cases j <;> norm_num [r0j19_lo, r0j19_hi]

end LeanLab.ChenDoubleSieve.Task661

#print axioms LeanLab.ChenDoubleSieve.Task661.short_hypotheses_nonempty
#print axioms LeanLab.ChenDoubleSieve.Task661.lower_corners_mem
