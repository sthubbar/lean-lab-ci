/-
P0073, page 427. Sufficient conditions for the original bounded seed search.
AI wrote this Lean code for CODEX task114. Goldbach is open.
-/
import LeanLab.Stein1965.Algorithm114

namespace LeanLab.Stein1965

/-- Page 427: a prime within the fuel window makes the bounded next-prime result sound. -/
theorem nextPrime_sound_of_witness (n fuel : ℕ)
    (hw : ∃ k < fuel, (n + k).Prime) :
    (nextPrime n fuel).Prime ∧ n ≤ nextPrime n fuel ∧ nextPrime n fuel < n + fuel := by
  induction fuel generalizing n with
  | zero => obtain ⟨k, hk, _⟩ := hw; omega
  | succ fuel ih =>
    by_cases hp : primeB n = true
    · rw [nextPrime, if_pos hp]
      exact ⟨primeB_sound hp, le_rfl, by omega⟩
    · obtain ⟨k, hk, hprime⟩ := hw
      have hkpos : 0 < k := by
        by_contra hn
        have hk0 : k = 0 := by omega
        subst k
        have hnprime : n.Prime := by simpa using hprime
        exact hp (LeanLab.SteinStein1965.primeB_complete hnprime)
      have hw' : ∃ j < fuel, (n + 1 + j).Prime := by
        refine ⟨k - 1, by omega, ?_⟩
        simpa only [show n + 1 + (k - 1) = n + k by omega] using hprime
      have hs := ih (n + 1) hw'
      rw [nextPrime, if_neg hp]
      exact ⟨hs.1, by omega, by omega⟩

/-- The bounded next-prime routine never returns below its starting point. -/
theorem nextPrime_ge (n fuel : ℕ) : n ≤ nextPrime n fuel := by
  induction fuel generalizing n with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [nextPrime]
    split
    · exact le_rfl
    · have hh := ih (n + 1)
      omega

/-- Page 427: the original bounded S-sequence contains primes when both seeds are prime. -/
theorem steinSeq_primes (p0 len : ℕ) (hp0 : p0.Prime) (hseed : (nextPrime (p0 + 1) 10).Prime) :
    ∀ a ∈ steinSeq p0 len, a.Prime := by
  unfold steinSeq
  apply List.foldlRecOn (motive := fun B : List ℕ => ∀ a ∈ B, a.Prime)
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hp0
    · exact hseed
  · intro B hB i hi a ha
    split at ha
    · rename_i q hq
      rcases List.mem_append.mp ha with ha | ha
      · exact hB a ha
      · have haq : a = q := List.mem_singleton.mp ha
        subst a
        exact (findNew_sound p0 B 100000 (2 * B.head! + 2) q hq).1
    · exact hB a ha

/-- Equations 2.2 and 2.3: the original bounded output never repeats an element. -/
theorem steinSeq_nodup (p0 len : ℕ) : (steinSeq p0 len).Nodup := by
  unfold steinSeq
  apply List.foldlRecOn (motive := fun B : List ℕ => B.Nodup)
  · have hne : p0 ≠ nextPrime (p0 + 1) 10 := by
      have hh := nextPrime_ge (p0 + 1) 10
      omega
    simp [hne]
  · intro B hB i hi
    split
    · rename_i q hq
      have hfresh := (findNew_sound p0 B 100000 (2 * B.head! + 2) q hq).2.2
      simp only [List.nodup_append, hB, List.nodup_singleton, true_and]
      intro a ha b hb hab
      have hb' : b = q := List.mem_singleton.mp hb
      subst b
      subst a
      exact hfresh ha
    · exact hB

end LeanLab.Stein1965
