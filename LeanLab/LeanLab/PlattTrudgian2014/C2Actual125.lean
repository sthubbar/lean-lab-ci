/-
AI wrote this Lean code. Binary Goldbach is open.
Platt and Trudgian arXiv 1404.5669v2 page 2 sums over odd integers 2d minus 1.
The sealed paperC2term instead uses Mersenne integers. It is preserved unchanged.
-/
import LeanLab.PlattTrudgian2014.PaperInputs
import LeanLab.Linnik.U1474R0

namespace LeanLab.PlattTrudgian2014

/-- The paper C2 term at d = j plus 1, with modulus 2j plus 1. -/
noncomputable def actualC2term125 (j : ℕ) : ℝ :=
  paperWeight (2 * j + 1) / (orderOf (2 : ZMod (2 * j + 1)) : ℝ)

/-- The actual odd modulus series on page 2. -/
noncomputable def actualC2_125 : ℝ := ∑' j : ℕ, actualC2term125 j

/-- CITED. Page 2 quotes Pintz 2006 Lemma 2 double prime for this actual C2 interval. -/
def PintzProductActual125 : Prop :=
  1.2783521041 < actualC2_125 * paperC0 ∧ actualC2_125 * paperC0 < 1.2784421041

/-- A concrete indexing discrepancy in the sealed lab model, not a paper error. -/
theorem paperC2term_third_mismatch125 :
    paperC2term 2 = (1 / 15 : ℝ) ∧ actualC2term125 2 = (1 / 12 : ℝ) := by
  have h5 : Odd 5 ∧ Squarefree 5 := by decide +kernel
  have h7 : Odd 7 ∧ Squarefree 7 := by decide +kernel
  have f5 : Nat.primeFactors 5 = {5} := by decide +kernel
  have f7 : Nat.primeFactors 7 = {7} := by decide +kernel
  change paperWeight 7 / (orderOf (2 : ZMod 7) : ℝ) = 1 / 15 ∧
    paperWeight 5 / (orderOf (2 : ZMod 5) : ℝ) = 1 / 12
  rw [Section2.eps_7, Section2.eps_5]
  norm_num [paperWeight, h5, h7, f5, f7]

/-- The actual paper term function differs from the sealed Mersenne term function. -/
theorem paperC2term_ne_actual125 : paperC2term ≠ actualC2term125 := by
  intro h
  have he := congrFun h 2
  rw [paperC2term_third_mismatch125.1, paperC2term_third_mismatch125.2] at he
  norm_num at he

/-- Reuse the lab's proved Romanov convergence theorem for the actual odd modulus series. -/
theorem actualC2_summable125 : Summable actualC2term125 := by
  have hf : Summable (fun d : ℕ => paperWeight d / (orderOf (2 : ZMod d) : ℝ)) := by
    simpa only [LeanLab.Linnik.U1466Display17.R0Summable,
      LeanLab.Linnik.U1464Display20.wt, LeanLab.Linnik.U1464Display20.eps, paperWeight] using
      LeanLab.Linnik.U1474R0.r0Summable
  have hi : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b h
    dsimp only at h
    omega
  change Summable (fun j : ℕ => paperWeight (2 * j + 1) /
    (orderOf (2 : ZMod (2 * j + 1)) : ℝ))
  exact hf.comp_injective hi

#print axioms paperC2term_third_mismatch125
#print axioms paperC2term_ne_actual125
#print axioms actualC2_summable125

end LeanLab.PlattTrudgian2014
