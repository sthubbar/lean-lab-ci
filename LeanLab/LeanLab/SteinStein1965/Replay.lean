/-
AI wrote this Lean code for CODEX task70.
Exact interval certificates for the S-algorithm, Section 2, page 427.
Each skipped even is checked as a pair sum. The next step uses the original rule.
-/
import LeanLab.SteinStein1965.Bitset

namespace LeanLab.SteinStein1965

def gapMask : ℕ → ℕ
  | 0 => 0
  | n + 1 => (gapMask n <<< 2) ||| 1

theorem gapMask_hit (n k : ℕ) (hk : k < n) : (gapMask n).testBit (2 * k) = true := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [gapMask, Nat.testBit_shiftLeft]
    | succ k =>
      have hh := ih k (by omega)
      simp only [gapMask, Nat.testBit_or, Nat.testBit_shiftLeft]
      have he : 2 * (k + 1) - 2 = 2 * k := by omega
      simp [he, hh, show 2 ≤ 2 * (k + 1) by omega]

def gapCheck (s : BitState) (lo n : ℕ) : Bool :=
  ((s.sums >>> lo) &&& gapMask n) == gapMask n

theorem gapCheck_sound (s : BitState) (lo n : ℕ) (h : gapCheck s lo n = true)
    (k : ℕ) (hk : k < n) : s.sums.testBit (lo + 2 * k) = true := by
  simp only [gapCheck, beq_iff_eq] at h
  have ht := congrArg (fun x : ℕ => x.testBit (2 * k)) h
  simpa only [Nat.testBit_and, gapMask_hit n k hk, Bool.and_true,
    Nat.testBit_shiftRight] using ht

theorem fold_fixed {α β : Type*} (f : α → β → α) (L : List β) (s : α)
    (h : ∀ b ∈ L, f s b = s) : L.foldl f s = s := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    rw [List.foldl_cons, h b List.mem_cons_self]
    exact ih (fun c hc => h c (List.mem_cons_of_mem b hc))

theorem gapFold (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (lo n : ℕ) (h : gapCheck s lo n = true) :
    (List.range' lo n 2).foldl (bitStep isA choose) s = s := by
  apply fold_fixed
  intro m hm
  obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hm
  simp [bitStep, gapCheck_sound s lo n h k hk]

def replayLength (gaps : List ℕ) : ℕ := (gaps.map (· + 1)).sum

def replay (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ) :
    List ℕ → ℕ → BitState → Option BitState
  | [], _, s => some s
  | d :: ds, lo, s =>
    if gapCheck s lo d then
      replay isA choose ds (lo + 2 * d + 2) (bitStep isA choose s (lo + 2 * d))
    else none

theorem replay_sound (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (gaps : List ℕ) (lo : ℕ) (s t : BitState)
    (h : replay isA choose gaps lo s = some t) :
    t = (List.range' lo (replayLength gaps) 2).foldl (bitStep isA choose) s := by
  induction gaps generalizing lo s with
  | nil => simpa [replay, replayLength] using h.symm
  | cons d ds ih =>
    simp only [replay] at h
    split at h
    · rename_i hg
      have ht := ih _ _ h
      have hl : replayLength (d :: ds) = d + (1 + replayLength ds) := by
        simp [replayLength, Nat.add_assoc]
      rw [hl, ← List.range'_append, List.foldl_append, gapFold isA choose s lo d hg]
      rw [Nat.add_comm 1 (replayLength ds), List.range'_succ, List.foldl_cons]
      convert ht using 1
    · contradiction

theorem replay_append (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (xs ys : List ℕ) (lo : ℕ) (s : BitState) :
    replay isA choose (xs ++ ys) lo s =
      (replay isA choose xs lo s).bind
        (fun t => replay isA choose ys (lo + 2 * replayLength xs) t) := by
  induction xs generalizing lo s with
  | nil => simp [replay, replayLength]
  | cons d ds ih =>
    simp only [List.cons_append, replay]
    by_cases hg : gapCheck s lo d = true
    · simp only [hg, ↓reduceIte]
      rw [ih]
      congr 1
      funext t
      congr 1
      simp [replayLength]
      omega
    · simp [hg]

theorem filter_even_range (lo n : ℕ) (hlo : lo % 2 = 0) :
    (List.range' lo (2 * n + 1)).filter (fun m => m % 2 == 0) =
      List.range' lo (n + 1) 2 := by
  induction n generalizing lo with
  | zero => simp [List.range'_succ, hlo]
  | succ n ih =>
    have he : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
    rw [he, List.range'_succ, List.range'_succ]
    simp only [List.filter_cons, hlo, beq_self_eq_true, ↓reduceIte]
    have hodd : ((lo + 1) % 2 == 0) = false := by
      have hm : (lo + 1) % 2 = 1 := by omega
      simp [hm]
    simp only [hodd, Bool.false_eq_true, ↓reduceIte]
    rw [show lo + 1 + 1 = lo + 2 by omega, ih (lo + 2) (by omega)]
    rfl

theorem evensIn_range (lo n : ℕ) (hlo : lo % 2 = 0) :
    evensIn lo (lo + 2 * n) = List.range' lo (n + 1) 2 := by
  unfold evensIn
  rw [show lo + 2 * n + 1 - lo = 2 * n + 1 by omega]
  exact filter_even_range lo n hlo

def listSummary (st : List ℕ × List ℕ) : ℕ × ℕ × List ℕ :=
  ((st.1.filter (· ≤ 200000)).length, st.1.length, st.2)

def runSummary (s : BitState) : ℕ × ℕ × List ℕ := listSummary s.view

theorem replay89_summary (choose : ℕ → Option ℕ → Option ℕ) (gaps : List ℕ)
    (n c l : ℕ) (fs : List ℕ) (hlen : replayLength gaps = n + 1)
    (hcheck : (replay (primeA 89) choose gaps 178 bitSeed89).map runSummary =
      some (c, l, fs)) :
    listSummary ((evensIn 178 (178 + 2 * n)).foldl (stepWith (primeA 89) choose)
      ([89, 97], [])) = (c, l, fs) := by
  obtain ⟨s, hs, hc⟩ := Option.map_eq_some_iff.mp hcheck
  have hv := congrArg BitState.view (replay_sound (primeA 89) choose gaps 178 bitSeed89 s hs)
  rw [hlen, ← evensIn_range 178 n (by decide)] at hv
  rw [bitFold_view _ _ _ _ bitSeed89_invariant (by decide)] at hv
  change s.view = _ at hv
  change listSummary s.view = _ at hc
  rw [hv] at hc
  exact hc

theorem replay_join (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (xs ys : List ℕ) (lo next : ℕ) (s t u : BitState)
    (hn : lo + 2 * replayLength xs = next)
    (hx : replay isA choose xs lo s = some t)
    (hy : replay isA choose ys next t = some u) :
    replay isA choose (xs ++ ys) lo s = some u := by
  rw [replay_append, hn, hx]
  exact hy

theorem replay_transport (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (xs ys : List ℕ) (lo : ℕ) (s t : BitState) (hxy : xs = ys)
    (h : replay isA choose xs lo s = some t) :
    replay isA choose ys lo s = some t := by
  subst ys
  exact h

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.gapMask_hit
#print axioms LeanLab.SteinStein1965.gapCheck_sound
#print axioms LeanLab.SteinStein1965.fold_fixed
#print axioms LeanLab.SteinStein1965.gapFold
#print axioms LeanLab.SteinStein1965.replay_sound
#print axioms LeanLab.SteinStein1965.filter_even_range
#print axioms LeanLab.SteinStein1965.evensIn_range
#print axioms LeanLab.SteinStein1965.replay89_summary

#print axioms LeanLab.SteinStein1965.replay_append

#print axioms LeanLab.SteinStein1965.replay_join
#print axioms LeanLab.SteinStein1965.replay_transport
