import LeanLab.ChenDoubleSieve.Decomp587g
import LeanLab.ChenDoubleSieve.Burst9Top

/-!
Non-vacuity and limitations of coarse bounds for the task662 certificate.
Source: https://arxiv.org/abs/0705.1652, pages 9, 26 and 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task662
open Wu04Functional Task587

/-- The two Buchstab hypotheses of the port have a joint witness.
Wu 2004 Lemma 2.10 page 9 with the zero extension convention. -/
theorem buchstab_hypotheses_inhabited :
    ∃ ω : ℝ → ℝ, IsBuchstab ω ∧ ZeroBelowOne ω := by
  obtain ⟨_, _, ω, _, hω⟩ := Task275.standard_functions
  exact ⟨Burst9Top.zeroExt ω, Burst9Top.zeroExt_isBuchstab hω,
    Burst9Top.zeroExt_zero ω⟩

/-- The uniform cap one leaves a polynomial certificate above the target.
This records a failed proof method, not a lower bound for the Buchstab integral.
Wu 2004 page 26, D2,18 and Table 1 row one page 30. -/
theorem r0j18_uniform_one_too_weak :
    ((155569 / 1000000000) : ℝ) <
      ∫ x in domain (fun j => (r0j18_lo j : ℝ)) (fun j => (r0j18_hi j : ℝ)),
        cellPoly 4 (2 : Fin 4) r0j18_lo r0j18_hi x := by
  rw [r0j18_polynomial_moment]
  norm_num

/-- The existing uniform and affine delay caps exceed the printed target.
This compares the proof method constants and does not refute the printed bound.
Wu 2004 Lemma 2.10 page 9. -/
theorem printed_tail_cap_not_from_affine :
    (561522 / 1000000 : ℝ) < 5618 / 10000 ∧
      (561522 / 1000000 : ℝ) < 31601 / 56250 := by
  norm_num

#print axioms buchstab_hypotheses_inhabited
#print axioms r0j18_uniform_one_too_weak
#print axioms printed_tail_cap_not_from_affine
end LeanLab.ChenDoubleSieve.Task662
