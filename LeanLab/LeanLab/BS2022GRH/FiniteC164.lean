/- AI wrote the Lean code for CODEX task164.
Finite reciprocal prime square bound for DecompJ278.
Journal p. 1221 display 6. Goldbach is open. -/
import LeanLab.BS2022GRH.Cert1575
import LeanLab.BS2022GRH.CertC164
namespace LeanLab.BS2022GRH.FiniteC164
open Real Finset Classical Cert1575 Cert1575Defs
/-- The finite natural sum from 1501 to 100501 is at most 7.885e-5.
The extra endpoint terms only increase this nonnegative bound. -/
theorem natural_sum_le : ∑ n ∈ Ico 1501 100501, a n ≤ (7.885e-5 : ℝ) := by
  have h0 := win_bound win00 (by norm_num) (by norm_num) (by norm_num) (hi := 3001) (by norm_num)
  have h1 := win_bound CertC164.finite_window (by norm_num) (by norm_num) (by norm_num)
    (hi := 100501) (by norm_num)
  have hs := chain (by norm_num : 1501 ≤ 3001) (by norm_num : 3001 ≤ 100501) h0 h1
  norm_num at hs
  linarith
/-- The exact finite_sum_le statement from the existing decomposition.
All prime indices satisfy 1500 at most p and p strictly below 100000. -/
theorem finite_sum_le :
    ∑' p : {p : ℕ // p.Prime ∧ 1500 ≤ (p : ℝ) ∧ (p : ℝ) < 100000},
      1 / ((p : ℕ) : ℝ) ^ 2 ≤ 7.885e-5 := by
  apply Real.tsum_le_of_sum_le (fun _ => by positivity)
  intro u
  have himg : ∑ x ∈ u, 1 / ((x : ℕ) : ℝ) ^ 2 =
      ∑ n ∈ u.image (fun x => x.1), a n := by
    rw [Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
    apply Finset.sum_congr rfl
    intro x _
    simp [a, x.2.1]
  rw [himg]
  have hsub : u.image (fun x => x.1) ⊆ Ico 1501 100501 := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hlow : 1500 ≤ x.1 := by exact_mod_cast x.2.2.1
    have hupp : x.1 < 100000 := by exact_mod_cast x.2.2.2
    have hne : x.1 ≠ 1500 := by
      intro h
      have hp := x.2.1
      rw [h] at hp
      exact not_prime_of_dvd (p := 2) le_rfl ⟨750, rfl⟩ (by norm_num) hp
    simp only [Finset.mem_Ico]
    omega
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => a_nonneg n)).trans natural_sum_le
end LeanLab.BS2022GRH.FiniteC164
#print axioms LeanLab.BS2022GRH.FiniteC164.natural_sum_le
#print axioms LeanLab.BS2022GRH.FiniteC164.finite_sum_le
