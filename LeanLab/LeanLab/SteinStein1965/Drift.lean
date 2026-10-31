/-
AI wrote this Lean code for CODEX task70.
Table I, page 430, and the maximum rule in equation 2.3, page 427.
A single changed choice is a diagnostic and is not attributed to the authors.
-/
import LeanLab.SteinStein1965.Base89Certificates
import LeanLab.SteinStein1965.Change89Certificates
import LeanLab.SteinStein1965.Choice450

namespace LeanLab.SteinStein1965

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def replaceAt (target candidate : ℕ) (m : ℕ) (original : Option ℕ) : Option ℕ :=
  if m = target then some candidate else original

def changedRun89 (target candidate N : ℕ) : List ℕ × List ℕ :=
  (evensIn 178 N).foldl (stepWith (primeA 89) (replaceAt target candidate)) ([89, 97], [])

theorem bitRun89_changed (target candidate N : ℕ) :
    (bitRun89 (replaceAt target candidate) N).view = changedRun89 target candidate N :=
  bitRun89_view _ _

theorem summary_original89 (N : ℕ) :
    listSummary ((evensIn 178 N).foldl (stepWith (primeA 89) (fun _ a => a))
      ([89, 97], [])) = listSummary (sPrime 89 N) := by
  rfl

theorem summary_changed89 (target candidate N : ℕ) :
    listSummary ((evensIn 178 N).foldl (stepWith (primeA 89) (replaceAt target candidate))
      ([89, 97], [])) = listSummary (changedRun89 target candidate N) := rfl

theorem replay89_summary_at (choose : ℕ → Option ℕ → Option ℕ) (gaps : List ℕ)
    (N n c l : ℕ) (fs : List ℕ) (hN : 178 + 2 * n = N)
    (hlen : replayLength gaps = n + 1)
    (hcheck : (replay (primeA 89) choose gaps 178 bitSeed89).map runSummary =
      some (c, l, fs)) :
    listSummary ((evensIn 178 N).foldl (stepWith (primeA 89) choose)
      ([89, 97], [])) = (c, l, fs) := by
  subst N
  exact replay89_summary choose gaps n c l fs hlen hcheck

theorem baseline89_counts :
    Bcount 89 200000 400000 = 1245 ∧ (sPrime 89 400000).1.length = 1809 ∧
      (sPrime 89 400000).2 = [180, 182, 184, 188] := by
  have h := replay89_summary_at (fun _ a => a) Base89AllGaps 400000 199911 1245 1809
    [180, 182, 184, 188] (by decide) (by decide +kernel) (by
      rw [Base89Full]
      decide +kernel)
  rw [summary_original89] at h
  simpa only [listSummary, Prod.mk.injEq, Bcount] using h

theorem changed89_counts :
    let st := changedRun89 450 223 400000
    (st.1.filter (· ≤ 200000)).length = 1246 ∧ st.1.length = 1816 ∧
      st.2 = [180, 182, 184, 188] := by
  have h := replay89_summary_at (replaceAt 450 223) Change89AllGaps 400000 199911 1246 1816
    [180, 182, 184, 188] (by decide) (by decide +kernel) (by
      unfold replaceAt
      rw [Change89Full]
      decide +kernel)
  rw [summary_changed89] at h
  simpa only [listSummary, Prod.mk.injEq] using h

theorem changedRun89_450 : changedRun89 450 223 450 =
    (prefix89 ++ [223], [180, 182, 184, 188]) := by
  decide +kernel

/-- The local replacement is at zero-based element index 25 and gives the first printed count. -/
theorem single_choice89_witness :
    (sPrime 89 448).1.length = 25 ∧
    (cands (primeA 89) (sPrime 89 448).1 450).max? = some 353 ∧
    223 ∈ cands (primeA 89) (sPrime 89 448).1 450 ∧
    Bcount 89 200000 400000 = 1245 ∧
    ((changedRun89 450 223 400000).1.filter (· ≤ 200000)).length = 1246 := by
  rw [prefix89_448]
  exact ⟨choice450.2.2.2.1, choice450.2.1, choice450.2.2.1,
    baseline89_counts.1, changed89_counts.1⟩

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.bitRun89_changed
#print axioms LeanLab.SteinStein1965.baseline89_counts
#print axioms LeanLab.SteinStein1965.changed89_counts
#print axioms LeanLab.SteinStein1965.changedRun89_450
#print axioms LeanLab.SteinStein1965.single_choice89_witness

#print axioms LeanLab.SteinStein1965.summary_original89
#print axioms LeanLab.SteinStein1965.summary_changed89

#print axioms LeanLab.SteinStein1965.replay89_summary_at
