/-
AI wrote this Lean code for CODEX task70.
Search complementary basis elements in ascending order to obtain the exact maximum candidate.
Section 2, equation 2.3, page 427.
-/
import LeanLab.SteinStein1965.Replay

namespace LeanLab.SteinStein1965

def seekAux (isA : ℕ → Bool) (bits m : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, lo =>
    if m < lo then none
    else if bits.testBit lo && isA (m - lo) then some (m - lo)
    else seekAux isA bits m fuel (lo + 1)

theorem seekAux_eq (isA : ℕ → Bool) (bits m : ℕ) (fuel lo : ℕ) (bs : List ℕ)
    (hbits : ∀ b, bits.testBit b = true ↔ b ∈ bs)
    (hmin : ∀ b ∈ bs, b ≤ m → isA (m - b) = true → lo ≤ b)
    (hcover : m < lo + fuel) :
    seekAux isA bits m fuel lo = (cands isA bs m).max? := by
  induction fuel generalizing lo with
  | zero =>
    have he : cands isA bs m = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      obtain ⟨ha, b, hb, hab⟩ := mem_cands ha
      have hb' : b ≤ m := by omega
      have hl := hmin b hb hb' (by simpa [show m - b = a by omega] using ha)
      omega
    simp [seekAux, he]
  | succ fuel ih =>
    by_cases hml : m < lo
    · have he : cands isA bs m = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro a ha
        obtain ⟨ha, b, hb, hab⟩ := mem_cands ha
        have hb' : b ≤ m := by omega
        have hl := hmin b hb hb' (by simpa [show m - b = a by omega] using ha)
        omega
      simp [seekAux, hml, he]
    · by_cases hh : bits.testBit lo = true ∧ isA (m - lo) = true
      · simp only [seekAux, if_neg hml, Bool.and_eq_true, hh, ↓reduceIte]
        symm
        apply List.max?_eq_some_iff.mpr
        constructor
        · apply List.mem_map.mpr
          refine ⟨lo, List.mem_filter.mpr ⟨(hbits lo).mp hh.1, ?_⟩, rfl⟩
          simp [hh.2, show lo ≤ m by omega]
        · intro a ha
          obtain ⟨ha, b, hb, hab⟩ := mem_cands ha
          have hb' : b ≤ m := by omega
          have hl := hmin b hb hb' (by simpa [show m - b = a by omega] using ha)
          omega
      · simp only [seekAux, if_neg hml, Bool.and_eq_true, if_neg hh]
        apply ih (lo + 1)
        · intro b hb hbm ha
          have hl := hmin b hb hbm ha
          have hn : b ≠ lo := by
            intro he
            subst b
            exact hh ⟨(hbits lo).mpr hb, ha⟩
          omega
        · omega

def Lower89 (s : BitState) : Prop := ∀ b ∈ s.basis, 89 ≤ b

def Choice89 (choose : ℕ → Option ℕ → Option ℕ) : Prop :=
  ∀ m d, (∀ a, d = some a → 89 ≤ a) → ∀ a, choose m d = some a → 89 ≤ a

def bitStepSeek (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (s : BitState) (m : ℕ) : BitState :=
  if s.sums.testBit m then s
  else match choose m (seekAux isA s.bits m (m + 1) 89) with
    | some a => bitAdd s a
    | none => { s with failures := s.failures ++ [m] }

theorem bitStepSeek_eq (choose : ℕ → Option ℕ → Option ℕ) (s : BitState) (m : ℕ)
    (hinv : BitInvariant s) (hlow : Lower89 s) :
    bitStepSeek (primeA 89) choose s m = bitStep (primeA 89) choose s m := by
  have hc := seekAux_eq (primeA 89) s.bits m (m + 1) 89 s.basis hinv.1
    (fun b hb _ _ => hlow b hb) (by omega)
  simp only [bitStepSeek, bitStep, hc, fastCand_eq (primeA 89) _ _ (by decide)]
  rfl

theorem bitStep_lower89 (choose : ℕ → Option ℕ → Option ℕ) (s : BitState) (m : ℕ)
    (hlow : Lower89 s) (hc : Choice89 choose) :
    Lower89 (bitStep (primeA 89) choose s m) := by
  unfold bitStep
  split
  · exact hlow
  · split
    · rename_i a ha
      have hd : ∀ a, fastCand (primeA 89) s.basis m = some a → 89 ≤ a := by
        intro a ha
        rw [fastCand_eq (primeA 89) _ _ (by decide)] at ha
        have hp := (mem_cands (List.max?_mem ha)).1
        exact ((primeA_iff 89 a).mp hp).1
      have hp := hc m _ hd a ha
      intro b hb
      simp only [bitAdd, List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hlow b hb
      · exact hp
    · exact hlow

theorem bitSeed_lower89 : Lower89 bitSeed89 := by
  intro b hb
  simp [bitSeed89, bitAdd, bitEmpty] at hb
  rcases hb with rfl | rfl <;> omega

def replaySeek (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ) :
    List ℕ → ℕ → BitState → Option BitState
  | [], _, s => some s
  | d :: ds, lo, s =>
    if gapCheck s lo d then
      replaySeek isA choose ds (lo + 2 * d + 2) (bitStepSeek isA choose s (lo + 2 * d))
    else none

theorem replaySeek_eq (choose : ℕ → Option ℕ → Option ℕ) (gaps : List ℕ)
    (lo : ℕ) (s : BitState) (hinv : BitInvariant s) (hlow : Lower89 s)
    (hc : Choice89 choose) :
    replaySeek (primeA 89) choose gaps lo s = replay (primeA 89) choose gaps lo s := by
  induction gaps generalizing lo s with
  | nil => rfl
  | cons d ds ih =>
    simp only [replaySeek, replay]
    by_cases hg : gapCheck s lo d = true
    · simp only [hg, ↓reduceIte]
      rw [bitStepSeek_eq choose s _ hinv hlow]
      exact ih _ _ (bitStep_invariant _ _ _ _ hinv) (bitStep_lower89 _ _ _ hlow hc)
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

theorem Choice89_identity : Choice89 (fun _ a => a) := by
  intro _ _ h
  exact h

theorem Choice89_replace (target candidate : ℕ) (ha : 89 ≤ candidate) :
    Choice89 (fun m a => if m = target then some candidate else a) := by
  intro m d hd a he
  by_cases hm : m = target
  · simp [hm] at he
    omega
  · simp [hm] at he
    exact hd a he

theorem replaySeek_join (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (xs ys : List ℕ) (lo next : ℕ) (s t u : BitState)
    (hn : lo + 2 * replayLength xs = next)
    (hx : replaySeek isA choose xs lo s = some t)
    (hy : replaySeek isA choose ys next t = some u) :
    replaySeek isA choose (xs ++ ys) lo s = some u := by
  rw [replaySeek_append, hn, hx]
  exact hy

theorem replaySeek_transport (isA : ℕ → Bool) (choose : ℕ → Option ℕ → Option ℕ)
    (xs ys : List ℕ) (lo : ℕ) (s t : BitState) (hxy : xs = ys)
    (h : replaySeek isA choose xs lo s = some t) :
    replaySeek isA choose ys lo s = some t := by
  subst ys
  exact h

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.seekAux_eq
#print axioms LeanLab.SteinStein1965.bitStepSeek_eq
#print axioms LeanLab.SteinStein1965.bitStep_lower89
#print axioms LeanLab.SteinStein1965.bitSeed_lower89
#print axioms LeanLab.SteinStein1965.replaySeek_eq
#print axioms LeanLab.SteinStein1965.replaySeek_append
#print axioms LeanLab.SteinStein1965.Choice89_identity
#print axioms LeanLab.SteinStein1965.Choice89_replace

#print axioms LeanLab.SteinStein1965.replaySeek_join
#print axioms LeanLab.SteinStein1965.replaySeek_transport
