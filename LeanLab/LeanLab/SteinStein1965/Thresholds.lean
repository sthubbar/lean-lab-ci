/-
AI wrote this Lean code for CODEX task70.
The two preceding admissible targets test the lower cutoffs in the note on pages 433 and 434.
The full cited range assertions are unchanged.
-/
import LeanLab.SteinStein1965.NoteAdded

namespace LeanLab.SteinStein1965

theorem leastGoldbachPrime_unique {N p q : ℕ}
    (hp : IsLeastGoldbachPrime N p) (hq : IsLeastGoldbachPrime N q) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · exact False.elim ((hq.2.2.2 p hp.1 h hp.2.1) hp.2.2.1)
  · exact h
  · exact False.elim ((hp.2.2.2 q hq.1 h hq.2.1) hq.2.2.1)

theorem leastP1Pair_unique {N p q : ℕ}
    (hp : IsLeastP1Pair N p) (hq : IsLeastP1Pair N q) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · exact False.elim ((hq.2.2.2 p h hp.2.1) hp.2.2.1)
  · exact h
  · exact False.elim ((hp.2.2.2 q h hq.2.1) hq.2.2.1)

def lowerCertP : List ℕ := [13, 151, 3, 3, 41, 3, 3, 17, 3, 3, 19, 5, 3, 5, 3, 3, 5, 3, 3, 37, 3, 3, 23, 7, 3, 191, 5, 3, 5, 3, 3, 5, 3, 3, 7, 3, 3, 7, 3, 3, 29, 5, 3, 5, 7, 3, 5, 3, 3, 11, 3, 3, 13, 3, 3, 7, 5, 3, 7, 11, 3, 5, 3, 3, 233, 7, 3, 19, 3, 3, 11, 5, 3, 5, 3, 3, 5, 3, 3, 7, 3, 3, 11, 13, 3, 89, 5, 3, 5, 3, 3, 5, 11, 3, 199, 3, 3, 7, 3, 3, 7, 5, 3, 11, 3, 3, 5, 7, 3, 13, 3, 3, 67, 3, 3, 11, 5, 3, 5, 3, 3, 5, 13, 3, 19, 11, 3, 29, 7, 3, 13, 5, 3, 5, 3, 3, 5, 3, 3, 7, 3, 3, 7, 17, 3]

theorem lowerCertP_ok : certOK 63274 2 3 lowerCertP = true ∧ lowerCertP.length = 145 := by
  decide +kernel

theorem leastPrime_63274 : IsLeastGoldbachPrime 63274 293 := by
  refine ⟨by decide, primeB_sound (by decide +kernel), primeB_sound (by decide +kernel), ?_⟩
  intro r h3 hr hp
  rcases Nat.even_or_odd r with he | ho
  · exact absurd (hp.even_iff.mp he) (by omega)
  · obtain ⟨j, rfl⟩ := ho
    have hk : j - 1 < lowerCertP.length := by rw [lowerCertP_ok.2]; omega
    have hh := certOK_sound 63274 2 lowerCertP 3 lowerCertP_ok.1 (j - 1) hk
    rw [show 3 + 2 * (j - 1) = 2 * j + 1 by omega] at hh
    rcases hh with hh | hh
    · exact False.elim (hh.2 hp)
    · exact hh.2

theorem square_bound_fails_63274 :
    ¬ ∃ q, IsLeastGoldbachPrime 63274 q ∧ q * q < 63274 := by
  rintro ⟨q, hq, hs⟩
  have he := leastGoldbachPrime_unique hq leastPrime_63274
  subst q
  norm_num at hs

def lowerCertP1 : List ℕ := [7, 3, 3, 11, 3, 3, 5, 3, 3, 5, 3, 3, 7, 3, 3, 29, 5, 3, 13, 7, 3, 5, 3, 3, 5, 3, 3, 269, 3, 3, 11, 5, 3, 7, 3, 3, 5, 3, 3, 5, 7, 3, 13, 3, 3, 613, 5, 3, 293, 3, 3, 5, 11, 3, 7, 13, 3, 13, 3, 3, 439, 5, 3, 11, 3, 3, 5, 3, 3, 5, 3, 3, 17, 3, 3, 7, 5, 3, 31, 3, 3, 5, 7, 3, 5, 11, 3, 257, 3, 3, 19, 5, 3, 113, 13, 3, 5, 3, 3, 5, 3, 3, 11, 7, 3, 7, 5, 3, 17, 19, 3, 5, 3, 3, 5, 3, 3, 7, 11, 3, 13, 5, 3, 17, 7, 3, 5, 3, 3, 11, 3, 3, 23, 13, 3, 11, 5, 3, 7, 3, 3, 5, 3, 3, 5, 7, 3, 19, 3, 3, 79, 5, 3, 229, 3, 3, 5, 17, 3, 7, 3, 3, 11, 3, 3, 571, 5, 3, 7, 3, 3, 5, 13, 3, 17, 3, 3, 467, 23, 3, 7, 5, 3, 383, 11, 3, 5, 7, 3, 5, 3, 3, 67, 3, 3, 11, 5, 3, 13, 3, 3, 5, 3, 3, 19, 3, 3, 43, 7, 3, 29, 5, 3, 13, 3, 3, 5, 11, 3, 5, 3, 3, 7, 19, 3, 17, 5, 3, 11, 7, 3, 5, 3, 3, 5, 3, 3, 13, 3, 3, 31, 5, 3, 7, 3, 3, 5, 23, 3, 5, 7, 3, 7, 3, 3, 97, 5, 3, 509, 17, 3, 5, 3, 3, 7, 3, 3, 11, 29, 3, 23, 5, 3, 7, 3, 3, 5, 3, 3, 5, 19, 3, 23, 11, 3, 7, 5, 3, 89, 13, 3, 5, 7, 3, 11, 3, 3, 29, 3, 3, 11, 5, 3, 53, 3, 3, 5, 3, 3, 5, 17, 3, 17, 7, 3, 13, 5, 3, 19, 3, 3, 5, 3, 3, 5, 3, 3, 7, 13, 3, 13, 5, 3, 31, 7, 3, 5, 19, 3, 23, 3, 3, 37, 3, 3]

theorem lowerCertP1_ok : certOK 1457282 4 1 lowerCertP1 = true ∧ lowerCertP1.length = 345 := by
  decide +kernel

theorem leastP1_1457282 : IsLeastP1Pair 1457282 1381 := by
  refine ⟨by decide, Or.inr ⟨primeB_sound (by decide +kernel), by decide⟩,
    Or.inr ⟨primeB_sound (by decide +kernel), by decide⟩, ?_⟩
  intro r hr h1 h2
  have hr4 : r % 4 = 1 := by
    rcases h1 with h1 | h1
    · omega
    · exact h1.2
  have hk : r / 4 < lowerCertP1.length := by rw [lowerCertP1_ok.2]; omega
  have hh := certOK_sound 1457282 4 lowerCertP1 1 lowerCertP1_ok.1 (r / 4) hk
  rw [show 1 + 4 * (r / 4) = r by omega] at hh
  rcases hh with hh | hh
  · rcases h1 with h1 | h1
    · omega
    · exact hh.2 h1.1
  · rcases h2 with h2 | h2
    · omega
    · exact hh.2 h2.1

theorem square_bound_fails_1457282 :
    ¬ ∃ q, IsLeastP1Pair 1457282 q ∧ q * q < 1457282 := by
  rintro ⟨q, hq, hs⟩
  have he := leastP1Pair_unique hq leastP1_1457282
  subst q
  norm_num at hs

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.leastGoldbachPrime_unique
#print axioms LeanLab.SteinStein1965.leastP1Pair_unique
#print axioms LeanLab.SteinStein1965.lowerCertP_ok
#print axioms LeanLab.SteinStein1965.leastPrime_63274
#print axioms LeanLab.SteinStein1965.square_bound_fails_63274
#print axioms LeanLab.SteinStein1965.lowerCertP1_ok
#print axioms LeanLab.SteinStein1965.leastP1_1457282
#print axioms LeanLab.SteinStein1965.square_bound_fails_1457282

namespace LeanLab.SteinStein1965

theorem leastPrime_half_bound {N q : ℕ} (he : N % 2 = 0)
    (hq : IsLeastGoldbachPrime N q) : 2 * q ≤ N := by
  have hrem := hq.2.2.1.two_le
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.2.1.odd_of_ne_two (by have := hq.1; omega))
  have hr3 : 3 ≤ N - q := by omega
  by_contra hn
  have hlt : N - q < q := by omega
  have hh := hq.2.2.2 (N - q) hr3 hlt hq.2.2.1
  rw [show N - (N - q) = q by omega] at hh
  exact hh hq.2.1

theorem leastP1_half_bound {N q : ℕ} (hq : IsLeastP1Pair N q) : 2 * q ≤ N := by
  by_contra hn
  have hlt : N - q < q := by omega
  have hh := hq.2.2.2 (N - q) hlt hq.2.2.1
  rw [show N - (N - q) = q by have := hq.1; omega] at hh
  exact hh hq.2.1

theorem half_bound_not_square_bound :
    ∃ q : ℕ, 2 * q ≤ 100000000 ∧ ¬ q * q < 100000000 := by
  exact ⟨50000000, by decide, by decide⟩

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.leastPrime_half_bound
#print axioms LeanLab.SteinStein1965.leastP1_half_bound
#print axioms LeanLab.SteinStein1965.half_bound_not_square_bound
