/-
Jia 1996 pages 252, 253 and 278 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp565b.iwaniec_transfer, the remaining regions of Lemma 28 group five.
The pair and triple Iwaniec transfers of displays 58 and 62 are separate leaves.
All source estimates remain OPEN. The assembly is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578a

namespace LeanLab.Languasco2004.Feed565bA
open Finset Real Decomp279a Decomp316a Source565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 283 display 58 for the remaining regions of page 285, with the page 278 linear sieve comparison. HARD.
CONDITIONAL ON the unchanged page 253 Lemma 17 input.
This estimates only the pair low cutoff count on the unselected pair domain. -/
theorem pair_sieve_transfer_rest (h17 : type_of% Decomp565c.lemma17_progression_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |pairMass false false N (localization N ε) n ((localization N ε) ^ delta ε) -
            singular n / log N * pairMass true false N (localization N ε) n ((localization N ε) ^ delta ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF: Jia page 284 display 62 for the remaining regions of page 285, with the page 278 linear sieve comparison. HARD.
The page 252 Lemma 16 progression estimate is needed outside its region i,
so no hypothesis from Decomp578a is assumed here.
This estimates only the triple low cutoff count on the unselected pair domain. -/
theorem triple_sieve_transfer_rest :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |tripleMass false false N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
            singular n / log N * tripleMass true false N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia displays 58 and 62 on page 285: exact type of Decomp565b.iwaniec_transfer.
CONDITIONAL ON the two leaves above and the unchanged Lemma 17 input. -/
theorem iwaniec_transfer_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.0000001 * scale N (localization N ε) n < iwaniecError false N (localization N ε) n ε)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  have h := Decomp578a.exceptional_add
    (fun ε N n => |pairMass false false N (localization N ε) n ((localization N ε) ^ delta ε) -
      singular n / log N * pairMass true false N (localization N ε) n ((localization N ε) ^ delta ε)|)
    (fun ε N n => |tripleMass false false N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
      singular n / log N * tripleMass true false N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)
    (fun ε N n => scale N (localization N ε) n) 0.0000001
    (by convert pair_sieve_transfer_rest Decomp565c.lemma17_progression_input using 1 <;> congr! <;> norm_num)
    (by convert triple_sieve_transfer_rest using 1 <;> congr! <;> norm_num)
  convert h using 1 <;> simp only [iwaniecError] <;> congr!

#print axioms pair_sieve_transfer_rest
#print axioms triple_sieve_transfer_rest
#print axioms iwaniec_transfer_from_leaves
end
end LeanLab.Languasco2004.Feed565bA
