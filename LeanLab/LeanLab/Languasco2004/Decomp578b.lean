/-
Jia 1996 pages 252, 253 and 278 to 284.
Source https://doi.org/10.4064/aa-77-3-207-287.
Separate source estimates for the region one transfers.
All source estimates remain OPEN. Assemblies are CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578a
import LeanLab.Languasco2004.Decomp565d
import LeanLab.Languasco2004.Feed578bPair
import LeanLab.Languasco2004.Feed578bTriple

namespace LeanLab.Languasco2004.Decomp578b
open Finset Real Decomp279a Decomp316a Source565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Jia page 283 display 59, using Lemma 19 on page 260.
CONDITIONAL ON the unchanged bounded rough weight input from Lemmas 5 and 18.
Only this one removed layer family is transferred. The other family is absent. -/
theorem pair_rough_transfer (h19 : type_of% Decomp565d.lemma19_rough_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |pairRemoved false true N (localization N ε) n ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ)) -
            singular n / log N * pairRemoved true true N (localization N ε) n ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ))|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := Feed578bPair.pair_rough_transfer_from_leaves h19

/-- LEAF. Jia page 284 display 63, using Lemma 19 on page 260.
CONDITIONAL ON the unchanged bounded rough weight input from Lemmas 5 and 18.
Only this one removed layer family is transferred. The other family is absent. -/
theorem triple_rough_transfer (h19 : type_of% Decomp565d.lemma19_rough_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |tripleRemoved false true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
            singular n / log N * tripleRemoved true true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := Feed578bTriple.triple_rough_transfer_from_leaves h19

/-- Jia displays 59 and 63: exact supplied type of the sealed lemma19_transfer.
CONDITIONAL ON the two proper removed layer leaves and the unchanged Lemma 19 input. -/
theorem lemma19_transfer_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.0000001 * scale N (localization N ε) n < lemma19Error true N (localization N ε) n ε)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  have h := Decomp578a.exceptional_add
    (fun ε N n => |pairRemoved false true N (localization N ε) n ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ)) -
            singular n / log N * pairRemoved true true N (localization N ε) n ((localization N ε) ^ delta ε) ((localization N ε) ^ (16 / 135 : ℝ))|)
    (fun ε N n => |tripleRemoved false true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε) -
            singular n / log N * tripleRemoved true true N (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ delta ε)|)
    (fun ε N n => scale N (localization N ε) n) 0.0000001
    (by convert pair_rough_transfer Decomp565d.lemma19_rough_input using 1 <;> congr! <;> norm_num)
    (by convert triple_rough_transfer Decomp565d.lemma19_rough_input using 1 <;> congr! <;> norm_num)
  convert h using 1 <;> simp only [lemma19Error] <;> congr!

#print axioms pair_rough_transfer
#print axioms triple_rough_transfer
#print axioms lemma19_transfer_from_parts
end
end LeanLab.Languasco2004.Decomp578b
