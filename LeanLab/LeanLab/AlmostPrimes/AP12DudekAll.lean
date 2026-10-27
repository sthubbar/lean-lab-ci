import LeanLab.AlmostPrimes.AP12FromTheta
import LeanLab.AlmostPrimes.U1504DudekAll

/-!
# Dudek's theorem from the modulus twelve theta input

AI wrote the Lean code. Goldbach is open.
Dudek, On the Sum of a Prime and a Square-free Number, Theorem 1, page 2,
https://arxiv.org/abs/1410.7459.
The finite check and even half are existing theorems. The odd half uses the
Ramaré and Rumely theta input through AP12FromTheta.
-/

namespace LeanLab.AlmostPrimes.AP12DudekAll

open AP12Theta AP12FromTheta

/-- Every integer N above two is a prime plus a positive square-free number.
CONDITIONAL ON RR12ThetaLower only. -/
theorem dudek_all_of_theta (h : RR12ThetaLower) (N : ℕ) (hN : 3 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m :=
  U1504DudekAll.dudek_all_ap12_pm (ap12Lower_of_theta h) N hN

/-- The same theorem from the complete printed table rows.
CONDITIONAL ON RR12Published.Published only. -/
theorem dudek_all_of_published (h : RR12Published.Published) (N : ℕ) (hN : 3 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m :=
  dudek_all_of_theta (RR12Published.lower_of_published h) N hN

end LeanLab.AlmostPrimes.AP12DudekAll

#print axioms LeanLab.AlmostPrimes.AP12DudekAll.dudek_all_of_theta
#print axioms LeanLab.AlmostPrimes.AP12DudekAll.dudek_all_of_published
