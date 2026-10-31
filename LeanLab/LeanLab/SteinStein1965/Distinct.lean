/-
AI wrote this Lean code for CODEX task70.
Section 2, equations 2.2 and 2.3, pages 427 and 428.
A new element cannot already belong to the basis, since its target is uncovered.
-/
import LeanLab.SteinStein1965.Seeds

namespace LeanLab.SteinStein1965

theorem fresh_candidate (isA : ℕ → Bool) (bs : List ℕ) (m a : ℕ)
    (hc : covers bs m = false) (ha : a ∈ cands isA bs m) : a ∉ bs := by
  intro hab
  obtain ⟨_, b, hb, he⟩ := mem_cands ha
  have ht := (covers_iff bs m).mpr ⟨a, hab, b, hb, he⟩
  rw [hc] at ht
  contradiction

theorem step_nodup (isA : ℕ → Bool) (st : List ℕ × List ℕ) (m : ℕ)
    (h : st.1.Nodup) : (step isA st m).1.Nodup := by
  unfold step
  split
  · exact h
  · rename_i hc
    split
    · rename_i a ha
      have hf := fresh_candidate isA st.1 m a (Bool.eq_false_iff.mpr hc) (List.max?_mem ha)
      simp only [List.nodup_append, h, List.nodup_singleton, true_and]
      intro b hb c hc he
      have hca : c = a := by simpa using hc
      subst c
      subst b
      exact hf hb
    · exact h

theorem foldl_nodup (isA : ℕ → Bool) (L : List ℕ) (st : List ℕ × List ℕ)
    (h : st.1.Nodup) : (L.foldl (step isA) st).1.Nodup := by
  induction L generalizing st with
  | nil => exact h
  | cons m L ih => exact ih _ (step_nodup _ _ _ h)

theorem sAlg_nodup (isA : ℕ → Bool) (a0 a1 N : ℕ) (hne : a0 ≠ a1) :
    (sAlg isA a0 a1 N).1.Nodup :=
  foldl_nodup _ _ _ (by simp [hne])

theorem sPrime_nodup (p0 N : ℕ) (hpos : 1 ≤ p0) : (sPrime p0 N).1.Nodup :=
  sAlg_nodup _ _ _ _ (Nat.ne_of_lt (nextA_gt p0 (nextA_prime p0 hpos)))

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.fresh_candidate
#print axioms LeanLab.SteinStein1965.step_nodup
#print axioms LeanLab.SteinStein1965.foldl_nodup
#print axioms LeanLab.SteinStein1965.sAlg_nodup

#print axioms LeanLab.SteinStein1965.sPrime_nodup
