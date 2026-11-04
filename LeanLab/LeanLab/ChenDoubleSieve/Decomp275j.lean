import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Lemma42

/-!
A concrete check of the forced-prime modulus convention in the Section 9 sums.
Source: https://arxiv.org/pdf/0705.1652, page 35 equation 9.4 and its proof on page 37.
This is a notation check. It is not a claim of a new error in the paper.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ChenDoubleSieve.Task275
open Finset Wu41

/-- The literal printed modulus would make each such quadruple term vanish.
This reuses the existing literal_zero theorem instead of reproving its sieve argument. -/
theorem literal_quadruple_zero (A : Finset ℕ) (N p1 p2 p3 p4 : ℕ)
    (hp1 : p1.Prime) (h12 : p1 < p2) (hc : p1.Coprime N) :
    S A (p1 * p2 * p3 * p4) N p2 = 0 := by
  have hnot : ¬ p1 ∣ 1 * N := by
    simpa only [one_mul] using (hp1.coprime_iff_not_dvd).1 hc
  have hd : p1 ∣ p1 * p2 * p3 * p4 :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right p1 p2) p3) p4
  simpa only [one_mul] using Wu42.literal_zero A 1 N (p1 * p2 * p3 * p4) hp1 h12 hnot hd

/-- A nonzero finite sieve instance distinguishes the two modulus readings.
It instantiates the generic convention, not the asymptotic prime difference sequence. -/
theorem modulus_convention_instance :
    S {1155} 1155 1000 5 = 0 ∧ S {1155} 1155 3000 5 = 1 := by
  constructor
  · have h := literal_quadruple_zero {1155} 1000 3 5 7 11
      (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · classical
    have hs : Sifted 3000 5 1155 := by
      intro q hq hq5 hqD
      have hqsmall : q < 5 := by exact_mod_cast hq5
      interval_cases q <;> norm_num at *
    have he : ∀ a ∈ ({1155} : Finset ℕ), 1155 ∣ a ∧ Sifted 3000 5 a := by
      intro a ha
      have ha' : a = 1155 := mem_singleton.mp ha
      subst a
      exact ⟨dvd_refl _, hs⟩
    unfold S
    rw [Finset.filter_eq_self.mpr he]
    exact card_singleton _

end LeanLab.ChenDoubleSieve.Task275
