/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Seed 3 replay of equations 2.2 and 2.3 on page 427.
-/
import LeanLab.SteinStein1965.Seek

namespace LeanLab.Stein1965.Replay3
open LeanLab.SteinStein1965

def bitSeed3 : BitState := bitAdd (bitAdd bitEmpty 3) 5

theorem bitSeed3_invariant : BitInvariant bitSeed3 :=
  bitAdd_invariant _ _ (bitAdd_invariant _ _ bitEmpty_invariant)

def bitRun3 (choose : ℕ → Option ℕ → Option ℕ) (N : ℕ) : BitState :=
  (evensIn 6 N).foldl (bitStep (primeA 3) choose) bitSeed3

theorem bitRun3_original (N : ℕ) :
    (bitRun3 (fun _ a => a) N).view = sPrime 3 N := by
  rw [bitRun3, bitFold_view _ _ _ _ bitSeed3_invariant (by decide)]
  rfl

def Lower3 (s : BitState) : Prop := ∀ b ∈ s.basis, 3 ≤ b

def Choice3 (choose : ℕ → Option ℕ → Option ℕ) : Prop :=
  ∀ m d, (∀ a, d = some a → 3 ≤ a) → ∀ a, choose m d = some a → 3 ≤ a

def bitStepSeek (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m : ℕ) : BitState :=
  if s.sums.testBit m then s
  else match choose m (seekAux isA s.bits m (m + 1) 3) with
    | some a => bitAdd s a
    | none => { s with failures := s.failures ++ [m] }

theorem bitStepSeek_eq (choose : ℕ → Option ℕ → Option ℕ) (s : BitState) (m : ℕ)
    (hinv : BitInvariant s) (hlow : Lower3 s) :
    bitStepSeek (primeA 3) choose s m = bitStep (primeA 3) choose s m := by
  have hc := seekAux_eq (primeA 3) s.bits m (m + 1) 3 s.basis hinv.1
    (fun b hb _ _ => hlow b hb) (by omega)
  simp only [bitStepSeek, bitStep, hc, fastCand_eq (primeA 3) _ _ (by decide)]
  rfl

theorem bitStep_lower3 (choose : ℕ → Option ℕ → Option ℕ) (s : BitState) (m : ℕ)
    (hlow : Lower3 s) (hc : Choice3 choose) :
    Lower3 (bitStep (primeA 3) choose s m) := by
  unfold bitStep
  split
  · exact hlow
  · split
    · rename_i a ha
      have hd : ∀ a, fastCand (primeA 3) s.basis m = some a → 3 ≤ a := by
        intro a ha
        rw [fastCand_eq (primeA 3) _ _ (by decide)] at ha
        have hp := (mem_cands (List.max?_mem ha)).1
        exact ((primeA_iff 3 a).mp hp).1
      have hp := hc m _ hd a ha
      intro b hb
      simp only [bitAdd, List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hlow b hb
      · exact hp
    · exact hlow

theorem bitSeed_lower3 : Lower3 bitSeed3 := by
  intro b hb
  simp [bitSeed3, bitAdd, bitEmpty] at hb
  rcases hb with rfl | rfl <;> omega

def replaySeek (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ) :
    List ℕ → ℕ → BitState → Option BitState
  | [], _, s => some s
  | d :: ds, lo, s =>
    if gapCheck s lo d then
      replaySeek isA choose ds (lo + 2 * d + 2) (bitStepSeek isA choose s (lo + 2 * d))
    else none

theorem replaySeek_eq (choose : ℕ → Option ℕ → Option ℕ) (gaps : List ℕ)
    (lo : ℕ) (s : BitState) (hinv : BitInvariant s) (hlow : Lower3 s)
    (hc : Choice3 choose) :
    replaySeek (primeA 3) choose gaps lo s = replay (primeA 3) choose gaps lo s := by
  induction gaps generalizing lo s with
  | nil => rfl
  | cons d ds ih =>
    simp only [replaySeek, replay]
    by_cases hg : gapCheck s lo d = true
    · simp only [hg, ↓reduceIte]
      rw [bitStepSeek_eq choose s _ hinv hlow]
      exact ih _ _ (bitStep_invariant _ _ _ _ hinv) (bitStep_lower3 _ _ _ hlow hc)
    · simp [hg]

theorem replaySeek_append (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (xs ys : List ℕ) (lo : ℕ) (s : BitState) :
    replaySeek isA choose (xs ++ ys) lo s =
      (replaySeek isA choose xs lo s).bind
        (fun t => replaySeek isA choose ys (lo + 2 * replayLength xs) t) := by
  induction xs generalizing lo s with
  | nil => simp [replaySeek, replayLength]
  | cons d ds ih =>
    simp only [List.cons_append, replaySeek]
    by_cases hg : gapCheck s lo d = true
    · simp only [hg, ↓reduceIte]
      rw [ih]
      congr 1
      funext t
      congr 1
      simp [replayLength]
      omega
    · simp [hg]

theorem Choice3_identity : Choice3 (fun _ a => a) := by
  intro _ _ h
  exact h


end LeanLab.Stein1965.Replay3
#print axioms LeanLab.Stein1965.Replay3.bitSeed3_invariant
#print axioms LeanLab.Stein1965.Replay3.bitRun3_original
#print axioms LeanLab.Stein1965.Replay3.bitStepSeek_eq
#print axioms LeanLab.Stein1965.Replay3.bitStep_lower3
#print axioms LeanLab.Stein1965.Replay3.bitSeed_lower3
#print axioms LeanLab.Stein1965.Replay3.replaySeek_eq
#print axioms LeanLab.Stein1965.Replay3.replaySeek_append
#print axioms LeanLab.Stein1965.Replay3.Choice3_identity
