/-
P0045, journal page 779, the estimate before display 29.
The sum of f over odd squarefree d at most D is bounded by a constant times log D.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.Lemma62Port
import LeanLab.LPZ2007.Lemma61Port

namespace LeanLab.LPZ2007.MontgomerySumProof

open Finset Real LeanLab.LPZ2007

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The divisor sum embeds in the Euler product over odd primes at most Y. -/
theorem sum_fd_le (D Y : ℕ) (hY : 4 ≤ Y) (hDY : D ≤ Y) :
    ∑ d ∈ (Icc 1 D).filter OddSqf, fd d ≤ exp 27 * log Y := by
  let Q := (Icc 3 Y).filter Nat.Prime
  have hinj : Set.InjOn Nat.primeFactors (↑((Icc 1 D).filter OddSqf)) := by
    intro a ha b hb hab
    have ha' := (mem_filter.1 ha).2.2
    have hb' := (mem_filter.1 hb).2.2
    rw [← Nat.prod_primeFactors_of_squarefree ha',
      ← Nat.prod_primeFactors_of_squarefree hb', hab]
  have hsub : ((Icc 1 D).filter OddSqf).image Nat.primeFactors ⊆ Q.powerset := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hs
    obtain ⟨hdI, ho⟩ := mem_filter.1 hd
    rw [mem_powerset]
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpD : p ≤ D := (Nat.le_of_dvd (mem_Icc.1 hdI).1 hpd).trans (mem_Icc.1 hdI).2
    have hp3 : 3 ≤ p := by
      have hne : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.2 ho.1) (even_iff_two_dvd.2 hpd)
      have := hpr.two_le
      omega
    exact mem_filter.2 ⟨mem_Icc.2 ⟨hp3, hpD.trans hDY⟩, hpr⟩
  calc
    (∑ d ∈ (Icc 1 D).filter OddSqf, fd d) ≤ ∑ s ∈ Q.powerset, LeanLab.LPZ2007B.W s := by
      refine sum_le_sum_of_injOn Nat.primeFactors hinj hsub ?_ ?_
      · intro d hd
        have ho := (mem_filter.1 hd).2
        exact le_of_eq (Lemma61Port.fd_eq ho)
      · intro s hs _
        exact LeanLab.LPZ2007B.W_nonneg (fun p hp => by
          have := (mem_Icc.1 (mem_filter.1 (mem_powerset.1 hs hp)).1).1
          omega)
    _ ≤ exp 27 * log Y := LeanLab.LPZ2007B.sum_W_small Y hY

/-- The Montgomery input holds with the explicit constant two times exp 27. -/
theorem montgomerySum_proved : MontgomerySum := by
  refine ⟨2 * exp 27, fun D hD => ?_⟩
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hlog : log (max D 4 : ℕ) ≤ 2 * log D := by
    have hmax : ((max D 4 : ℕ) : ℝ) ≤ (D : ℝ) ^ 2 := by
      rw [Nat.cast_max]
      apply max_le <;> push_cast <;> nlinarith
    have := log_le_log (by positivity : (0 : ℝ) < (max D 4 : ℕ)) hmax
    rwa [Real.log_pow] at this
  calc ∑ d ∈ (Icc 1 D).filter OddSqf, fd d ≤ exp 27 * log (max D 4 : ℕ) :=
      sum_fd_le D (max D 4) (le_max_right _ _) (le_max_left _ _)
    _ ≤ exp 27 * (2 * log D) := mul_le_mul_of_nonneg_left hlog (exp_pos _).le
    _ = (2 * exp 27) * log D := by ring

end
end LeanLab.LPZ2007.MontgomerySumProof

#print axioms LeanLab.LPZ2007.MontgomerySumProof.sum_fd_le
#print axioms LeanLab.LPZ2007.MontgomerySumProof.montgomerySum_proved

namespace LeanLab.LPZ2007

/-- The former cited declaration, now proved with its exact original statement. -/
theorem montgomerySum : MontgomerySum := MontgomerySumProof.montgomerySum_proved

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.montgomerySum
