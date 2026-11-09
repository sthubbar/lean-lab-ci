/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Supply mode split of the scalar part of the remainder leaf.
The sealed DecompC164c file is unchanged.
Journal pp. 1239 and 1240, displays 31 and 32.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Bilinear339
import LeanLab.BS2022GRH.Balance339
import LeanLab.BS2022GRH.Decomp339c
import LeanLab.BS2022GRH.SliceInstances236
import LeanLab.BS2022GRH.Decomp406e

namespace LeanLab.BS2022GRH.Decomp339a
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- The bilinear main budget before summing slices, journal p. 1240 display 32. -/
def mainScale (n : ℕ) (A ε₁ : ℝ) : ℝ :=
  mbarJ n A (U7153.zz n) * n * √(1 + ε₁) / log n ^ (A - 1)

/-- The coprimality budget before summing slices, journal p. 1240 display 32. -/
def correctionScale (n : ℕ) (ε₁ : ℝ) : ℝ :=
  (1 + ε₁) * (n : ℝ) ^ (7 / 8 : ℝ) * log n ^ 2

/-- LEAF. Only the two remaining cutoff guards in the Lemma 8 substitution.
Journal p. 1239 after the definitions of X, Y, Z and D star.
The lower ranges and D star bound are proved by task236.
The other two cutoff guards are proved in Cutoff339.
No residue estimate, GRH statement or mbar comparison is included. -/
theorem cutoff_guards (α A u X₂ ε₁ : ℝ) (n j : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hj : j ∈ slices n ε₁) :
    let X := (n : ℝ) / w n ε₁ j
    let Y := min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)
    let D := √(n : ℝ) / log n ^ (A + 1)
    √(X * Y) / D ≤ Decomp148a.cutoff Y ∧ Decomp148a.cutoff Y ≤ D := by
  exact ⟨Balance339.slice_balancing α A u X₂ ε₁ n j hε hε1 hα hα1 hA hc hX hn hj,
    Cutoff339.cutoff_le_Dstar α A u X₂ ε₁ n j hε hε1 hα hα1 hA hc hX hn hj⟩

/-- LEAF. Only the coefficient comparisons and scale normalization of display 31.
Journal pp. 1239 and 1240, from w at least N to one eighth and w at most sqrt N over two.
This is a scalar statement with no residue, modulus sum, GRH or threshold transfer.
It includes m at X, Y and D star at most mbar at w and then at N to one eighth. -/
theorem slice_scale_bound (α A u X₂ ε₁ : ℝ) (n j : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hj : j ∈ slices n ε₁) :
    let X := (n : ℝ) / w n ε₁ j
    let Y := min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)
    let D := √(n : ℝ) / log n ^ (A + 1)
    Decomp148a.mJ X Y D * Decomp148a.scale X Y D ≤ mainScale n A ε₁ / 4 := by
  exact Decomp339c.slice_scale_assembly α A u X₂ ε₁ n j hε hε1 hα hα1 hA hc hX hn hj

/-- The finite rectangle and Lemma 8 leave only the scalar main budget.
CONDITIONAL ON Lemma 8 and the two smaller scalar leaves above.
Journal pp. 1239 and 1240 display 32. -/
theorem reduced_slice_bound (h8 : Decomp148a.Lemma8J) (hG : GRH)
    (α A u X₂ ε₁ : ℝ) (n j : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) (hj : j ∈ slices n ε₁) :
    (∑ d ∈ divisors n A, |SliceRemainder236.reducedResidue n j d ε₁|) ≤
      mainScale n A ε₁ / 4 := by
  have hN := hX.trans hn
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hN
  have hnN : 0 < n := by exact_mod_cast hn0
  have hr := SliceRemainder236.slice_bilinear_basic_ranges n j ε₁ hN hε hε1 hj
  have hD := SliceRemainder236.slice_Dstar_ge α A u X₂ n hα hα1 hA hc hX hn
  have hg := cutoff_guards α A u X₂ ε₁ n j hε hε1 hα hα1 hA hc hX hn hj
  have h8b := h8 hG (Bilinear339.coefficient n j ε₁) _ _ _ _ n
    (fun m => Bilinear339.coefficient_norm n j m ε₁)
    hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 (by linarith)
    (Cutoff339.Dstar_lt_rectangle n j A ε₁ hN hε hε1 hA hj) hg.1
    (le_min hg.2 (Cutoff339.cutoff_le_sqrt _ _ hr.2.2.1 hr.2.2.2.1.le hr.2.2.2.2))
    (by exact_mod_cast hev : Even (n : ℤ))
  exact ((Bilinear339.reduced_sum_le_bilinear n j A ε₁ hnN hε).trans h8b).trans
    (slice_scale_bound α A u X₂ ε₁ n j hε hε1 hα hα1 hA hc hX hn hj)

/-- A first slice certifies nonnegativity of the scalar budget.
CONDITIONAL ON the same scalar leaves and Lemma 8, journal p. 1240 display 32. -/
theorem mainScale_nonneg (h8 : Decomp148a.Lemma8J) (hG : GRH)
    (α A u X₂ ε₁ : ℝ) (n : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) : 0 ≤ mainScale n A ε₁ := by
  have hj := SliceRemainder236.zero_mem_slices n ε₁ (hX.trans hn) hε
  have hs := reduced_slice_bound h8 hG α A u X₂ ε₁ n 0 hε hε1 hα hα1 hA hc hX hn hev hj
  have h0 : (0 : ℝ) ≤ ∑ d ∈ divisors n A,
      |SliceRemainder236.reducedResidue n 0 d ε₁| := sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

/-- Full per-slice residue estimate from independent main and correction arguments.
CONDITIONAL ON Lemmas 4, 5 and 8 and the scalar leaves above.
Journal p. 1240 display 32. -/
theorem slice_bound (h4 : PaperInputs148.Lemma4J) (hPhi : PaperInputs148.Lemma5PhiJ)
    (h8 : Decomp148a.Lemma8J) (hG : GRH) (α A u X₂ ε₁ : ℝ) (n j : ℕ)
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) (hj : j ∈ slices n ε₁) :
    (∑ d ∈ divisors n A, |residueError n ε₁ j d|) ≤
      mainScale n A ε₁ / 4 + 0.374 * correctionScale n ε₁ := by
  exact (SliceRemainder236.slice_remainder_split n j A ε₁).trans
    (add_le_add
      (reduced_slice_bound h8 hG α A u X₂ ε₁ n j hε hε1 hα hα1 hA hc hX hn hev hj)
      (Correction339.correction_bound h4 hPhi n j A ε₁ (hX.trans hn) hA hε
        (SliceRemainder236.slice_Dstar_ge α A u X₂ n hα hα1 hA hc hX hn)))

end
end LeanLab.BS2022GRH.Decomp339a
#print axioms LeanLab.BS2022GRH.Decomp339a.cutoff_guards
#print axioms LeanLab.BS2022GRH.Decomp339a.slice_scale_bound
#print axioms LeanLab.BS2022GRH.Decomp339a.reduced_slice_bound
#print axioms LeanLab.BS2022GRH.Decomp339a.mainScale_nonneg
#print axioms LeanLab.BS2022GRH.Decomp339a.slice_bound
