/-
AI wrote this Lean code for CODEX task128.
P0073, Table IV, pages 431 and 432.
Every positive consecutive-prime gap except the gap from 2 to 3 is even.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

/-- Table IV, page 432: no odd gap other than one occurs between consecutive primes. -/
theorem gapCount_odd_eq_zero (X g : ℕ) (hg : Odd g) (hne : g ≠ 1) :
    gapCount X g = 0 := by
  apply List.length_eq_zero_iff.mpr
  apply List.filter_eq_nil_iff.mpr
  intro p hp htest
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
  obtain ⟨⟨⟨hpb, _⟩, hqb⟩, hmid⟩ := htest
  have hP := primeB_sound hpb
  have hQ := primeB_sound hqb
  have hmod : g % 2 = 1 := Nat.odd_iff.mp hg
  have hg3 : 3 ≤ g := by omega
  by_cases hp2 : p = 2
  · have hthree : 3 ∈ List.range' (p + 1) (g - 1) := by
      rw [List.mem_range'_1]
      omega
    have hnot := List.all_eq_true.mp hmid 3 hthree
    have hprime : primeB 3 = true := primeB_complete Nat.prime_three
    simp [hprime] at hnot
  · have hpo := Nat.odd_iff.mp (hP.odd_of_ne_two hp2)
    have hq2 : p + g ≠ 2 := by have := hP.two_le; omega
    have hqo := Nat.odd_iff.mp (hQ.odd_of_ne_two hq2)
    omega

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.gapCount_odd_eq_zero
