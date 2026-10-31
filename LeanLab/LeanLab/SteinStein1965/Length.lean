/-
AI wrote this Lean code for CODEX task70.
Section 2, equation 2.3, page 427. Each scanned target adds at most one element.
The generic bound is too weak to prove the exact count in Section 5, page 433.
-/
import LeanLab.SteinStein1965.Replay

namespace LeanLab.SteinStein1965

theorem step_length_le (isA : ℕ → Bool) (st : List ℕ × List ℕ) (m : ℕ) :
    (step isA st m).1.length ≤ st.1.length + 1 := by
  unfold step
  split
  · omega
  · split <;> simp <;> omega

theorem fold_length_le (isA : ℕ → Bool) (L : List ℕ) (st : List ℕ × List ℕ) :
    (L.foldl (step isA) st).1.length ≤ st.1.length + L.length := by
  induction L generalizing st with
  | nil => simp
  | cons m L ih =>
    have hh := ih (step isA st m)
    have hs := step_length_le isA st m
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem sAlg_length_le (isA : ℕ → Bool) (a0 a1 N : ℕ) :
    (sAlg isA a0 a1 N).1.length ≤ 2 + (evensIn (2 * a0) N).length :=
  fold_length_le _ _ _

theorem sPrime_length_le (p0 N : ℕ) :
    (sPrime p0 N).1.length ≤ 2 + (evensIn (2 * p0) N).length :=
  sAlg_length_le _ _ _ _

theorem Bcount_le_length (p0 x N : ℕ) :
    Bcount p0 x N ≤ (sPrime p0 N).1.length :=
  List.length_filter_le _ _

theorem claim7_generic_bound : Bcount 7 7000000 7000000 ≤ 3499996 ∧ 13108 < 3499996 := by
  constructor
  · have hs := sPrime_length_le 7 7000000
    have he := congrArg List.length (evensIn_range 14 3499993 (by decide))
    norm_num only [Nat.reduceMul, Nat.reduceAdd, List.length_range'] at he
    norm_num only [Nat.reduceMul] at hs
    rw [he] at hs
    exact le_trans (Bcount_le_length 7 7000000 7000000) (by
      simpa only [Nat.reduceAdd] using hs)
  · decide

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.step_length_le
#print axioms LeanLab.SteinStein1965.fold_length_le
#print axioms LeanLab.SteinStein1965.sAlg_length_le
#print axioms LeanLab.SteinStein1965.claim7_generic_bound

#print axioms LeanLab.SteinStein1965.sPrime_length_le
#print axioms LeanLab.SteinStein1965.Bcount_le_length
