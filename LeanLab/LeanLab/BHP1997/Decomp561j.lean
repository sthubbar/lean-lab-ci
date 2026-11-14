/-
P0069 page 3 and page 9 display 2.13, a nonunit support diagnostic.
These finite identities isolate an unresolved source obligation. They do not
prove the asymptotic hypotheses or negate the sealed local energy leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561c
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace LeanLab.BHP1997.Decomp561j
open Classical Complex AddCircle Finset

/-- P0069 page 3 and page 9 display 2.13, an even supported additive phase
used to test the nonunit part of the short polynomial. -/
noncomputable def evenPhaseCoeff561 (t : ℝ) (m : ℕ) : ℂ :=
  if Even m then @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ)) else 0

/-- P0069 page 3 hypothesis ii, the diagnostic coefficients are bounded by 1. -/
theorem evenPhaseCoeff_norm_le561 (t : ℝ) (m : ℕ) :
    ‖evenPhaseCoeff561 t m‖ ≤ 1 := by
  unfold evenPhaseCoeff561
  split_ifs
  · rw [fourier_apply, Circle.norm_coe]
  · simp

/-- P0069 page 9 display 2.13, every character of even modulus is blind to
this even supported coefficient. This does not address odd moduli. -/
theorem even_modulus_twist_zero561 (t : ℝ) {q : ℕ} (hq : Even q)
    (χ : DirichletCharacter ℂ q) (m : ℕ) :
    evenPhaseCoeff561 t m * χ (m : ZMod q) = 0 := by
  by_cases hm : Even m
  · have hnot : ¬ Nat.Coprime m q := by
      intro hc
      have hd : 2 ∣ Nat.gcd m q := Nat.dvd_gcd
        (even_iff_two_dvd.mp hm) (even_iff_two_dvd.mp hq)
      rw [hc.gcd_eq_one] at hd
      norm_num at hd
    have hu : ¬ IsUnit (m : ZMod q) := by
      rwa [ZMod.isUnit_iff_coprime]
    rw [χ.map_nonunit hu, mul_zero]
  · simp [evenPhaseCoeff561, hm]

/-- P0069 page 9 displays 2.11 and 2.13, the additive peak is the full even
support cardinality despite the vanishing even modulus character twists. -/
theorem even_phase_peak561 (S : Finset ℕ) (t : ℝ) :
    (∑ m ∈ S, evenPhaseCoeff561 t m *
      @fourier 1 (-(m : ℤ)) (t : AddCircle (1 : ℝ))) =
        ((S.filter Even).card : ℂ) := by
  calc
    _ = ∑ m ∈ S, if Even m then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases he : Even m
      · simp only [evenPhaseCoeff561, he, ite_true]
        rw [← fourier_add]
        simp
      · simp [evenPhaseCoeff561, he]
    _ = _ := by simp [Finset.sum_boole]

end LeanLab.BHP1997.Decomp561j
