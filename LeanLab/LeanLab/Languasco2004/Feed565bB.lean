/-
Jia 1996 pages 260 and 283 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp565b.lemma19_transfer, the remaining regions of Lemma 28 group five.
The pair and triple removed layer transfers of displays 59 and 63 are separate leaves.
All source estimates remain OPEN. The assembly is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578a
import LeanLab.Languasco2004.Decomp565d

namespace LeanLab.Languasco2004.Feed565bB
open Finset Real Decomp279a Decomp316a Source565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 283 display 59 for the remaining regions of page 285, using Lemma 19 on page 260. HARD.
CONDITIONAL ON the unchanged bounded rough weight input from Lemmas 5 and 18.
Only the pair removed layer family on the unselected pair domain is transferred. -/
theorem pair_rough_transfer_rest (h19 : type_of% Decomp565d.lemma19_rough_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |pairRemoved false false N (localization N ε) n ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ)) -
            singular n / log N * pairRemoved true false N (localization N ε) n ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ))|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- LEAF: Jia page 284 display 63 for the remaining regions of page 285, using Lemma 19 on page 260. HARD.
CONDITIONAL ON the unchanged bounded rough weight input from Lemmas 5 and 18.
Only the triple removed layer family on the unselected pair domain is transferred. -/
theorem triple_rough_transfer_rest (h19 : type_of% Decomp565d.lemma19_rough_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |tripleRemoved false false N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
            singular n / log N * tripleRemoved true false N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia displays 59 and 63 on page 285: exact type of Decomp565b.lemma19_transfer.
CONDITIONAL ON the two leaves above and the unchanged Lemma 19 input. -/
theorem lemma19_transfer_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.0000001 * scale N (localization N ε) n < lemma19Error false N (localization N ε) n ε)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  have h := Decomp578a.exceptional_add
    (fun ε N n => |pairRemoved false false N (localization N ε) n ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ)) -
            singular n / log N * pairRemoved true false N (localization N ε) n ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ))|)
    (fun ε N n => |tripleRemoved false false N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
            singular n / log N * tripleRemoved true false N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)
    (fun ε N n => scale N (localization N ε) n) 0.0000001
    (by convert pair_rough_transfer_rest Decomp565d.lemma19_rough_input using 1 <;> congr! <;> norm_num)
    (by convert triple_rough_transfer_rest Decomp565d.lemma19_rough_input using 1 <;> congr! <;> norm_num)
  convert h using 1 <;> simp only [lemma19Error] <;> congr!

#print axioms pair_rough_transfer_rest
#print axioms triple_rough_transfer_rest
#print axioms lemma19_transfer_from_leaves
end
end LeanLab.Languasco2004.Feed565bB
