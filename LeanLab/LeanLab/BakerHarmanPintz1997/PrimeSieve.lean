/-
P0069, page 32, equation 4.24. The prime indicator at a square root sieve cutoff.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Prop12
import LeanLab.BakerHarmanPintz1997.Buchstab

namespace LeanLab.BakerHarmanPintz1997
attribute [local instance] Classical.propDecidable

/-- A prime is rough at every cutoff at most that prime. -/
theorem rough_of_prime {n : ℕ} {z : ℝ} (hn : n.Prime) (hz : z ≤ (n : ℝ)) : Rough n z := by
  intro p hp hpz hpn
  have heq : p = n := ((hn.dvd_iff_eq hp.ne_one).mp hpn).symm
  subst p
  linarith

/-- Equation 4.24 uses the prime indicator as a rough indicator below the square cutoff. -/
theorem psi_eq_primeIndicator {n : ℕ} {z : ℝ} (hn : 2 ≤ n) (hz : 0 ≤ z)
    (hzn : z ≤ (n : ℝ)) (hsize : (n : ℝ) < z ^ 2) :
    psi n z = (primeIndicator n : ℂ) := by
  have hr : Rough n z ↔ n.Prime :=
    ⟨prime_of_rough_of_lt_sq hn hz hsize, fun hp => rough_of_prime hp hzn⟩
  simp only [psi, primeIndicator, hr]
  split_ifs <;> norm_num

#print axioms rough_of_prime
#print axioms psi_eq_primeIndicator
end LeanLab.BakerHarmanPintz1997
