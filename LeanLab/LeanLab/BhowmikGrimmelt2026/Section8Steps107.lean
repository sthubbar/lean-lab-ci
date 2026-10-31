/-
Local counting and sign steps from the proof of Theorem 8.2 on page 32.
The existing decomposition in ExceptionalSet is not repeated here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Beta84
import LeanLab.BhowmikGrimmelt2026.Counting107

namespace LeanLab.BhowmikGrimmelt2026

attribute [local instance] Classical.propDecidable

/-- LEAF. Page 32, second paragraph. A finite set survives removal of two smaller sets. -/
theorem exists_outside_two107 (S B E : Finset ℕ)
    (hcard : (B.card : ℝ) + (E.card : ℝ) < S.card) :
    ∃ N ∈ S, N ∉ B ∧ N ∉ E := by
  have hn : B.card + E.card < S.card := by exact_mod_cast hcard
  obtain ⟨N, hN, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card
    ((Finset.card_union_le B E).trans_lt hn)
  exact ⟨N, hN, by simpa only [Finset.mem_union, not_or] using hout⟩

/-- LEAF. Page 32, final paragraph. A character evaluated at minus one is one or minus one. -/
theorem character_neg_one107 {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    χ (-1) = 1 ∨ χ (-1) = -1 := by
  apply sq_eq_one_iff.mp
  calc
    (χ (-1)) ^ 2 = χ ((-1 : ZMod r) ^ 2) := (map_pow χ (-1) 2).symm
    _ = 1 := by simp

/-- LEAF. Page 32, final paragraph. Either sign contradicts the two sided interval. -/
theorem sign_contradiction107 {a s δ : ℝ} (hδ : 0 < δ)
    (hrange : δ * s ≤ a ∧ a ≤ (2 - δ) * s) {z : ℂ} (hz : z = 1 ∨ z = -1)
    (hnear : ‖(a : ℂ) - (1 + z) * (s : ℂ)‖ < δ * s) : False := by
  have hreal := (Complex.abs_re_le_norm ((a : ℂ) - (1 + z) * (s : ℂ))).trans_lt hnear
  rcases hz with hz | hz
  · rw [hz] at hreal
    norm_num at hreal
    have := neg_le_abs (a - 2 * s)
    nlinarith [hrange.2]
  · rw [hz] at hreal
    norm_num at hreal
    nlinarith [hrange.1, le_abs_self a]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.exists_outside_two107
#print axioms LeanLab.BhowmikGrimmelt2026.character_neg_one107
#print axioms LeanLab.BhowmikGrimmelt2026.sign_contradiction107
