/-
AI wrote this Lean code for CODEX task70.
Exact bitset implementation of Section 2, equations 2.2 and 2.3, page 427.
-/
import LeanLab.SteinStein1965.Fast

namespace LeanLab.SteinStein1965

structure BitState where
  basis : List ℕ
  failures : List ℕ
  bits : ℕ
  sums : ℕ
  deriving DecidableEq

def BitState.view (s : BitState) : List ℕ × List ℕ := (s.basis, s.failures)

def BitInvariant (s : BitState) : Prop :=
  (∀ m, s.bits.testBit m = true ↔ m ∈ s.basis) ∧
  (∀ m, s.sums.testBit m = true ↔ covers s.basis m = true)

def bitEmpty : BitState := ⟨[], [], 0, 0⟩

def bitAdd (s : BitState) (a : ℕ) : BitState :=
  ⟨s.basis ++ [a], s.failures, s.bits ||| (1 <<< a),
   s.sums ||| (s.bits <<< a) ||| (1 <<< (a + a))⟩

theorem singletonBit (a m : ℕ) : (1 <<< a).testBit m = true ↔ a = m := by
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
    Nat.testBit_one_eq_true_iff_self_eq_zero]
  omega

theorem bitEmpty_invariant : BitInvariant bitEmpty := by
  simp [BitInvariant, bitEmpty, covers]

theorem bitAdd_invariant (s : BitState) (a : ℕ) (h : BitInvariant s) :
    BitInvariant (bitAdd s a) := by
  obtain ⟨hb, hs⟩ := h
  constructor
  · intro m
    simp only [bitAdd, Nat.testBit_or, Bool.or_eq_true, singletonBit, hb,
      List.mem_append, List.mem_singleton]
    exact or_congr Iff.rfl eq_comm
  · intro m
    have ht : (s.bits <<< a).testBit m = true ↔ ∃ b ∈ s.basis, a + b = m := by
      simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, hb]
      constructor
      · rintro ⟨ha, hm⟩
        exact ⟨m - a, hm, by omega⟩
      · rintro ⟨b, hb, hab⟩
        exact ⟨by omega, by simpa [show m - a = b by omega] using hb⟩
    simp only [bitAdd, Nat.testBit_or, Bool.or_eq_true, hs, ht, singletonBit, covers_add]
    aesop

/-- A diagnostic can change the candidate at a specified target. -/
def stepWith (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (st : List ℕ × List ℕ) (m : ℕ) : List ℕ × List ℕ :=
  if covers st.1 m then st
  else match choose m (cands isA st.1 m).max? with
    | some a => (st.1 ++ [a], st.2)
    | none => (st.1, st.2 ++ [m])

def bitStep (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m : ℕ) : BitState :=
  if s.sums.testBit m then s
  else match choose m (fastCand isA s.basis m) with
    | some a => bitAdd s a
    | none => { s with failures := s.failures ++ [m] }

theorem bitStep_invariant (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m : ℕ) (h : BitInvariant s) :
    BitInvariant (bitStep isA choose s m) := by
  unfold bitStep
  split
  · exact h
  · split
    · exact bitAdd_invariant s _ h
    · exact h

theorem bitStep_view (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m : ℕ) (h : BitInvariant s) (h0 : isA 0 = false) :
    (bitStep isA choose s m).view = stepWith isA choose s.view m := by
  have hc : s.sums.testBit m = covers s.basis m := by
    have hh := h.2 m
    cases hs : s.sums.testBit m <;> cases hb : covers s.basis m <;> simp_all
  simp only [bitStep, stepWith, BitState.view, hc, fastCand_eq isA _ _ h0]
  by_cases hh : covers s.basis m = true
  · simp [hh]
  · cases ho : choose m (cands isA s.basis m).max? <;> simp [hh, ho, bitAdd]

theorem bitFold_invariant (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (L : List ℕ) (s : BitState) (h : BitInvariant s) :
    BitInvariant (L.foldl (bitStep isA choose) s) := by
  induction L generalizing s with
  | nil => exact h
  | cons m L ih => exact ih _ (bitStep_invariant _ _ _ _ h)

theorem bitFold_view (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (L : List ℕ) (s : BitState) (h : BitInvariant s) (h0 : isA 0 = false) :
    (L.foldl (bitStep isA choose) s).view = L.foldl (stepWith isA choose) s.view := by
  induction L generalizing s with
  | nil => rfl
  | cons m L ih =>
    rw [List.foldl_cons, List.foldl_cons, ih _ (bitStep_invariant _ _ _ _ h),
      bitStep_view _ _ _ _ h h0]

def bitSeed89 : BitState := bitAdd (bitAdd bitEmpty 89) 97

theorem bitSeed89_invariant : BitInvariant bitSeed89 :=
  bitAdd_invariant _ _ (bitAdd_invariant _ _ bitEmpty_invariant)

def bitRun89 (choose : ℕ → Option ℕ → Option ℕ) (N : ℕ) : BitState :=
  (evensIn 178 N).foldl (bitStep (primeA 89) choose) bitSeed89

theorem bitRun89_view (choose : ℕ → Option ℕ → Option ℕ) (N : ℕ) :
    (bitRun89 choose N).view =
      (evensIn 178 N).foldl (stepWith (primeA 89) choose) ([89, 97], []) := by
  exact bitFold_view _ _ _ _ bitSeed89_invariant (by decide)

theorem bitRun89_original (N : ℕ) :
    (bitRun89 (fun _ a => a) N).view = sPrime 89 N := by
  rw [bitRun89_view]
  rfl

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.singletonBit
#print axioms LeanLab.SteinStein1965.bitEmpty_invariant
#print axioms LeanLab.SteinStein1965.bitAdd_invariant
#print axioms LeanLab.SteinStein1965.bitStep_invariant
#print axioms LeanLab.SteinStein1965.bitStep_view
#print axioms LeanLab.SteinStein1965.bitFold_invariant
#print axioms LeanLab.SteinStein1965.bitFold_view
#print axioms LeanLab.SteinStein1965.bitSeed89_invariant
#print axioms LeanLab.SteinStein1965.bitRun89_view
#print axioms LeanLab.SteinStein1965.bitRun89_original
