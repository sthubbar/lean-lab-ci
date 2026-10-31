/-
AI wrote this Lean code for CODEX task128.
P0073, Section 3, page 428, uniqueness of the sequence for a fixed input.
Only input membership at most the largest scanned target is relevant.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

/-- Equation 2.3, page 427: candidates depend only on input membership up to the target. -/
theorem cands_congr_bounded (isA isB : ℕ → Bool) (bs : List ℕ) (m N : ℕ)
    (hAB : ∀ n ≤ N, isA n = isB n) (hm : m ≤ N) :
    cands isA bs m = cands isB bs m := by
  unfold cands
  congr 1
  apply List.filter_congr
  intro b hb
  rw [hAB (m - b) (le_trans (Nat.sub_le m b) hm)]

/-- Equations 2.2 and 2.3, pages 427 and 428: the next state is determined locally. -/
theorem step_congr_bounded (isA isB : ℕ → Bool) (st : List ℕ × List ℕ) (m N : ℕ)
    (hAB : ∀ n ≤ N, isA n = isB n) (hm : m ≤ N) :
    step isA st m = step isB st m := by
  unfold step
  rw [cands_congr_bounded isA isB st.1 m N hAB hm]

/-- Section 3, page 428: finite scans agree for input predicates agreeing on their targets. -/
theorem scan_congr_bounded (isA isB : ℕ → Bool) (L : List ℕ)
    (st : List ℕ × List ℕ) (N : ℕ)
    (hAB : ∀ n ≤ N, isA n = isB n) (hL : ∀ m ∈ L, m ≤ N) :
    L.foldl (step isA) st = L.foldl (step isB) st := by
  induction L generalizing st with
  | nil => rfl
  | cons m L ih =>
    rw [List.foldl_cons, List.foldl_cons, step_congr_bounded isA isB st m N hAB
      (hL m (by simp))]
    exact ih _ (fun k hk => hL k (by simp [hk]))

/-- Section 3, page 428: the S-sequence is determined by the finite relevant input set. -/
theorem sAlg_congr_bounded (isA isB : ℕ → Bool) (a0 a1 N : ℕ)
    (hAB : ∀ n ≤ N, isA n = isB n) :
    sAlg isA a0 a1 N = sAlg isB a0 a1 N := by
  exact scan_congr_bounded isA isB _ _ N hAB (fun _ hm => (mem_evensIn.mp hm).2.1)

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.cands_congr_bounded
#print axioms LeanLab.SteinStein1965.step_congr_bounded
#print axioms LeanLab.SteinStein1965.scan_congr_bounded
#print axioms LeanLab.SteinStein1965.sAlg_congr_bounded
