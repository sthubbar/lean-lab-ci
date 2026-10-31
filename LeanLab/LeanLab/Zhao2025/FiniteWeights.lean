import LeanLab.Zhao2025.Display110Sum

/-!
The exact finite zero sums behind S, T and R.
Source: Zhao 2025, display 2.28 on page 7 and display 3.14 on page 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- The finite inner sum in display 1.10. -/
noncomputable def zeroSum {ι : Type*} (z : Finset ι) (lam : ι → ℝ) : ℝ :=
  ∑ j ∈ z, Real.exp (-(10 / 3 * lam j))

/-- The capped sum T of display 3.14. -/
noncomputable def cappedSum {ι : Type*} (z : Finset ι) (lam : ι → ℝ) (L : ℝ) : ℝ :=
  ∑ j ∈ z, Real.exp (-(10 / 3 * max (lam j) L))

/-- The residual R is S minus T, as defined in display 3.14. -/
noncomputable def residualSum {ι : Type*} (z : Finset ι) (lam : ι → ℝ) (L : ℝ) : ℝ :=
  zeroSum z lam - cappedSum z lam L

/-- The required sign and splitting identities hold without cited inputs. -/
theorem weight_split {ι : Type*} (z : Finset ι) (lam : ι → ℝ) (L : ℝ) :
    0 ≤ residualSum z lam L ∧ 0 ≤ cappedSum z lam L ∧
      zeroSum z lam = residualSum z lam L + cappedSum z lam L := by
  have ht : cappedSum z lam L ≤ zeroSum z lam := by
    apply Finset.sum_le_sum
    intro j _
    apply Real.exp_le_exp.mpr
    have h := le_max_left (lam j) L
    linarith
  have ht0 : 0 ≤ cappedSum z lam L := Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
  unfold residualSum
  exact ⟨sub_nonneg.mpr ht, ht0, by ring⟩

#print axioms weight_split

end LeanLab.Zhao2025.Task56
