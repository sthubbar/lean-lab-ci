/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3, pages 9 and 10.
A nonempty concrete instance of the new averaging set interface.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSLemma43Model

namespace LeanLab.Ternary.MMS
open Finset

/-- The averaging interface has a witness with a qualifying nonempty progression. -/
theorem lemma43_bohr_nonvacuous :
    ∃ K : ℝ, 1 ≤ K ∧
      Prop31Hyp 24 (1 / 2) (1 / 6) K (5 / 2) (fun _ => 1) ∧
      Lemma43Data 24 (1 / 2) (1 / 6) K (5 / 2) (1 / 24) 24 (fun _ => 1)
        (intSmooth {0} (intervalLift 24 (fun _ => 1)))
        (intervalLift 24 (fun _ => 1) - intSmooth {0} (intervalLift 24 (fun _ => 1))) ∧
      IsAPIn 24 (Icc 1 24) ∧
      ((1 / 2 : ℝ) + (1 / 24) / (1 / 6)) * 24 ≤ (Icc 1 24).card := by
  obtain ⟨K, hK, h⟩ := prop31Hyp_one 24 (by norm_num)
  have hf := h (1 / 2) (by norm_num)
  refine ⟨K, hK, hf, ?_, isAPIn_Icc (by norm_num) le_rfl, by norm_num⟩
  have hmodel := lemma43Data_of_bohr (δ := 1 / 24) hf (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ({0} : Finset ℤ) (by simp) (κ := 1 / 24) (by norm_num) (by norm_num)
    (by
      intro a ha b hb
      simp only [mem_singleton] at ha hb
      subst a
      subst b
      norm_num)
    (by
      intro γ hγ b hb
      simp only [mem_singleton] at hb
      subst b
      exact ⟨0, by norm_num⟩)
  norm_num at hmodel ⊢
  exact hmodel

end LeanLab.Ternary.MMS
