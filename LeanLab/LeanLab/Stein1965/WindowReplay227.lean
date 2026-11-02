/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Bounded event replay for pages 427 through 429.
-/
import LeanLab.Stein1965.Window227

namespace LeanLab.Stein1965.WindowReplay227
open LeanLab.SteinStein1965
open LeanLab.Stein1965.Replay3
open LeanLab.Stein1965.Mask227
open LeanLab.Stein1965.Window227

theorem gapMask_lt (n : ℕ) : gapMask n < 2 ^ (2 * n) := by
  have h := gapMask_geometric n
  have he : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; rfl
  rw [he] at h
  omega

theorem and_clip (x mask width : ℕ) (hm : mask < 2 ^ width) :
    (x % 2 ^ width) &&& mask = x &&& mask := by
  have h := Nat.and_mod_two_pow (a := x) (b := mask) (n := width)
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (Nat.and_lt_two_pow x hm)] at h
  exact h.symm

theorem gapCheck_window (s : BitState) (lo cap d : ℕ) (hd : lo + 2 * d ≤ cap + 1) :
    gapCheckClosed (window s lo cap) 0 d = gapCheck s lo d := by
  have hb : gapMask d < 2 ^ (cap + 1 - lo) :=
    lt_of_lt_of_le (gapMask_lt d) (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [gapCheckClosed_eq, gapCheck, window, slice, Nat.shiftRight_zero,
    and_clip _ _ _ hb]

/-- Ascending candidate search in a moving sum window. -/
def windowSeekStep (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m cap : ℕ) : BitState :=
  if s.sums.testBit 0 then s
  else match choose m (seekAux (primeA 3) s.bits m (m + 1) 3) with
    | some a => windowAdd s a m cap
    | none => { s with failures := s.failures ++ [m] }

theorem windowSeekStep_eq (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m cap : ℕ) (hm : m ≤ cap)
    (hinv : BitInvariant s) (hlow : Lower3 s) :
    windowSeekStep choose (window s m cap) m cap =
      window (bitStep (primeA 3) choose s m) m cap := by
  have hc := seekAux_eq (primeA 3) s.bits m (m + 1) 3 s.basis hinv.1
    (fun b hb _ _ => hlow b hb) (by omega)
  rw [← windowStep_eq (primeA 3) choose s m cap hm]
  simp only [windowSeekStep, windowStep, window, hc,
    fastCand_eq (primeA 3) _ _ (by decide)]
  rfl

/-- Check each skipped interval and forget obsolete sum bits after each event. -/
def windowReplay (choose : ℕ → Option ℕ → Option ℕ) :
    List ℕ → ℕ → ℕ → BitState → Option BitState
  | [], _, _, s => some s
  | d :: ds, lo, cap, s =>
    if gapCheckClosed s 0 d then
      let m := lo + 2 * d
      let atEvent := advance s (2 * d) (cap + 1 - m)
      let stepped := windowSeekStep choose atEvent m cap
      let next := advance stepped 2 (cap + 1 - (m + 2))
      windowReplay choose ds (m + 2) cap next
    else none

theorem windowReplay_eq (choose : ℕ → Option ℕ → Option ℕ)
    (gaps : List ℕ) (lo cap : ℕ) (s : BitState)
    (hinv : BitInvariant s) (hlow : Lower3 s) (hc : Choice3 choose)
    (hbound : lo + 2 * replayLength gaps ≤ cap + 2) :
    windowReplay choose gaps lo cap (window s lo cap) =
      (replay (primeA 3) choose gaps lo s).map
        (fun t => window t (lo + 2 * replayLength gaps) cap) := by
  induction gaps generalizing lo s with
  | nil => simp [windowReplay, replay, replayLength]
  | cons d ds ih =>
    have hlen : replayLength (d :: ds) = d + 1 + replayLength ds := by
      simp [replayLength, Nat.add_assoc]
    have hm : lo + 2 * d ≤ cap := by rw [hlen] at hbound; omega
    simp only [windowReplay, replay, gapCheck_window s lo cap d (by omega)]
    by_cases hg : gapCheck s lo d = true
    · simp only [hg, ↓reduceIte]
      have ha := advance_window s lo (lo + 2 * d) cap (by omega)
      rw [show lo + 2 * d - lo = 2 * d by omega] at ha
      rw [ha, windowSeekStep_eq choose s _ cap hm hinv hlow]
      have hb := advance_window (bitStep (primeA 3) choose s (lo + 2 * d))
        (lo + 2 * d) (lo + 2 * d + 2) cap (by omega)
      rw [show lo + 2 * d + 2 - (lo + 2 * d) = 2 by omega] at hb
      rw [hb, ih _ _ (bitStep_invariant _ _ _ _ hinv)
        (bitStep_lower3 _ _ _ hlow hc) (by rw [hlen] at hbound; omega)]
      congr 1
      funext t
      congr 1
      rw [hlen]
      omega
    · simp [hg]


theorem windowReplay_append (choose : ℕ → Option ℕ → Option ℕ)
    (xs ys : List ℕ) (lo cap : ℕ) (s : BitState) :
    windowReplay choose (xs ++ ys) lo cap s =
      (windowReplay choose xs lo cap s).bind
        (fun t => windowReplay choose ys (lo + 2 * replayLength xs) cap t) := by
  induction xs generalizing lo s with
  | nil => simp [windowReplay, replayLength]
  | cons d ds ih =>
    simp only [List.cons_append, windowReplay]
    by_cases hg : gapCheckClosed s 0 d = true
    · simp only [hg, ↓reduceIte]
      rw [ih]
      congr 1
      funext t
      congr 1
      simp [replayLength]
      omega
    · simp [hg]

theorem windowReplay_join (choose : ℕ → Option ℕ → Option ℕ)
    (xs ys : List ℕ) (lo next cap : ℕ) (s t u : BitState)
    (hn : lo + 2 * replayLength xs = next)
    (hx : windowReplay choose xs lo cap s = some t)
    (hy : windowReplay choose ys next cap t = some u) :
    windowReplay choose (xs ++ ys) lo cap s = some u := by
  rw [windowReplay_append, hn, hx]
  exact hy

theorem windowReplay_seed3_view (gaps : List ℕ) (n : ℕ) (t : BitState)
    (hlen : replayLength gaps = n + 1)
    (hcheck : windowReplay (fun _ a => a) gaps 6 (6 + 2 * n)
      (window bitSeed3 6 (6 + 2 * n)) = some t) :
    t.view = sPrime 3 (6 + 2 * n) := by
  rw [windowReplay_eq _ _ _ _ _ bitSeed3_invariant bitSeed_lower3 Choice3_identity
    (by rw [hlen]; omega)] at hcheck
  obtain ⟨s, hs, ht⟩ := Option.map_eq_some_iff.mp hcheck
  have hv := congrArg BitState.view
    (replay_sound (primeA 3) (fun _ a => a) gaps 6 bitSeed3 s hs)
  rw [hlen, ← evensIn_range 6 n (by decide)] at hv
  have ho := bitRun3_original (6 + 2 * n)
  change (List.foldl _ bitSeed3 _).view = _ at ho
  rw [← hv] at ho
  rw [← ht]
  exact ho

end LeanLab.Stein1965.WindowReplay227
#print axioms LeanLab.Stein1965.WindowReplay227.gapMask_lt
#print axioms LeanLab.Stein1965.WindowReplay227.and_clip
#print axioms LeanLab.Stein1965.WindowReplay227.gapCheck_window
#print axioms LeanLab.Stein1965.WindowReplay227.windowSeekStep_eq
#print axioms LeanLab.Stein1965.WindowReplay227.windowReplay_eq

#print axioms LeanLab.Stein1965.WindowReplay227.windowReplay_append
#print axioms LeanLab.Stein1965.WindowReplay227.windowReplay_join
#print axioms LeanLab.Stein1965.WindowReplay227.windowReplay_seed3_view
