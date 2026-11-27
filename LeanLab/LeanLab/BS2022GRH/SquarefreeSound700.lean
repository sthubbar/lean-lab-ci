/- AI wrote this Lean code for CODEX task700. Goldbach is open.
Soundness of the finite squarefree counting certificate for Buthe 2014 display 4.6.
https://arxiv.org/abs/1410.7561v2 -/
import LeanLab.BS2022GRH.Witness700
import Mathlib

namespace LeanLab.BS2022GRH.SquarefreeSound700
open Real Finset Witness700
noncomputable section

/-- The exact count of squarefree positive integers up to N. -/
def sqCount (N : ℕ) : ℕ := ((Icc 1 N).filter (fun n => Squarefree n)).card

/-- Every accepted square divisor is a valid exclusion from the squarefree count. -/
theorem excludes_not_squarefree (n d : ℕ) (h : excludes n d = true) : ¬ Squarefree n := by
  simp only [excludes, decide_eq_true_eq] at h
  intro hs
  have hu := hs d (Nat.dvd_of_mod_eq_zero h.2)
  rw [Nat.isUnit_iff] at hu
  omega

/-- A checked exclusion gives a one sided upper bound for the next count. -/
theorem sqCount_succ_le (n d : ℕ) :
    sqCount (n+1) ≤ sqCount n + (if excludes (n+1) d then 0 else 1) := by
  unfold sqCount
  rw [card_filter, card_filter, sum_Icc_succ_top (by omega)]
  cases he : excludes (n+1) d
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> omega
  · have hn := excludes_not_squarefree (n+1) d he
    simp [hn]

/-- The trace checker bounds the final count and every intervening count. -/
theorem verify_sound (rows : List (ℕ × ℕ × ℕ)) :
    ∀ n q N Q : ℕ, sqCount n ≤ q → verify rows n q N Q = true →
      sqCount N ≤ Q ∧ ∀ m : ℕ, n < m → m ≤ N →
        ∃ c : ℕ, sqCount m ≤ c ∧ good m c = true := by
  induction rows with
  | nil =>
      intro n q N Q hq h
      simp only [verify, decide_eq_true_eq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨hq, by intro m hm hm'; omega⟩
  | cons row rows ih =>
      rcases row with ⟨m,d,c⟩
      intro n q N Q hq h
      simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hstep,hcount⟩,hgood⟩,hrest⟩ := h
      subst m
      have hbound : sqCount (n+1) ≤ c := by
        rw [hcount]
        exact (sqCount_succ_le n d).trans (Nat.add_le_add_right hq _)
      have hr := ih (n+1) c N Q hbound hrest
      refine ⟨hr.1, ?_⟩
      intro j hj hjN
      rcases Nat.lt_or_ge (n+1) j with hnext | hnext
      · exact hr.2 j hnext hjN
      · have hjeq : j=n+1 := by omega
        subst j
        exact ⟨c, hbound, hgood⟩

end
end LeanLab.BS2022GRH.SquarefreeSound700

#print axioms LeanLab.BS2022GRH.SquarefreeSound700.excludes_not_squarefree
#print axioms LeanLab.BS2022GRH.SquarefreeSound700.sqCount_succ_le
#print axioms LeanLab.BS2022GRH.SquarefreeSound700.verify_sound
