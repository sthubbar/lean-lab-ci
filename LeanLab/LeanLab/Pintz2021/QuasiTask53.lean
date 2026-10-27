import LeanLab.Pintz2021.Statements

/-!
The arithmetic quasi-divisor step of P0054 page 7 displays 2.12 to 2.14.
The character product conductor is supplied as an integer parameter.
Actual exceptional characters and their analytic estimates remain conditional.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.QuasiTask53

/-- A bounded reduced denominator gives a common factorial multiple. -/
theorem quasi_divisor_of_ratio_le {r m B : ℕ} (hr : 0 < r)
    (hB : r / Nat.gcd r m ≤ B) : r ∣ B.factorial * m := by
  have hg : 0 < Nat.gcd r m := Nat.gcd_pos_of_pos_left m hr
  have hratio : 0 < r / Nat.gcd r m :=
    Nat.div_pos (Nat.gcd_le_left m hr) hg
  have hd : r / Nat.gcd r m ∣ B.factorial := Nat.dvd_factorial hratio hB
  have hmul := Nat.mul_dvd_mul hd (Nat.gcd_dvd_right r m)
  simpa only [Nat.div_mul_cancel (Nat.gcd_dvd_left r m)] using hmul

/-- Exact divisibility after removing the common factor with m. -/
theorem ratio_dvd_iff {r m C : ℕ} (hr : 0 < r) :
    r / Nat.gcd r m ∣ C ↔ r ∣ C * m := by
  constructor
  · intro h
    have hmul := Nat.mul_dvd_mul h (Nat.gcd_dvd_right r m)
    simpa only [Nat.div_mul_cancel (Nat.gcd_dvd_left r m)] using hmul
  · intro h
    have hg : 0 < Nat.gcd r m := Nat.gcd_pos_of_pos_left m hr
    have hmul : Nat.gcd r m * (r / Nat.gcd r m) ∣
        Nat.gcd r m * (C * (m / Nat.gcd r m)) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left r m), mul_left_comm,
        Nat.mul_div_cancel' (Nat.gcd_dvd_right r m)]
      exact h
    have hdiv := Nat.dvd_of_mul_dvd_mul_left hg hmul
    exact (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_right hdiv

/-- The maximum in display 2.12 with the product conductor supplied as c. -/
def quasiSize (r s m c : ℕ) : ℕ :=
  max (max (r ^ 2 / Nat.gcd r s ^ 2) (s ^ 2 / Nat.gcd r s ^ 2))
    (max (max (r / Nat.gcd r m) (s / Nat.gcd s m)) c)

/-- Bounded maximum gives the arithmetic conclusions of display 2.14. -/
theorem quasiSize_le_implies {r s m c B : ℕ} (hr : 0 < r) (hs : 0 < s)
    (h : quasiSize r s m c ≤ B) :
    r ∣ B.factorial * m ∧ s ∣ B.factorial * m ∧ c ≤ B := by
  simp only [quasiSize, max_le_iff] at h
  exact ⟨quasi_divisor_of_ratio_le hr h.2.1.1,
    quasi_divisor_of_ratio_le hs h.2.1.2, h.2.2⟩

end LeanLab.Pintz2021.QuasiTask53

#print axioms LeanLab.Pintz2021.QuasiTask53.quasi_divisor_of_ratio_le
#print axioms LeanLab.Pintz2021.QuasiTask53.ratio_dvd_iff
#print axioms LeanLab.Pintz2021.QuasiTask53.quasiSize_le_implies
