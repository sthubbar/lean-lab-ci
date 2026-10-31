/-
AI wrote this Lean code for CODEX task58.
Two exact rational mass certificates for the centered nested integral polynomials.
The certificates alone do not identify real integrals.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58PolyTerms

namespace LeanLab.ChenPrimeExceptional.Task58

/-- The rational approximation used for log of three halves. -/
def logThreeHalvesQ : ℚ := 2 * ((List.range 8).map
  (fun i : ℕ => (1 / 5 : ℚ) ^ (2 * i + 1) / (2 * (i : ℚ) + 1))).sum

/-- Logarithm terms in the centered variable z. -/
def centeredLogTerms : Terms := (logThreeHalvesQ, 0) :: (List.range 20).map
  (fun i : ℕ => (-(-1 : ℚ) ^ (i + 1) / ((i : ℚ) + 1) * (2 / 3 : ℚ) ^ (i + 1), i + 1))

/-- Reciprocal inner-kernel terms in z. -/
def centeredReciprocalTerms : Terms := (List.range 16).map
  (fun j : ℕ => ((2 / 5 : ℚ) * (-2 / 5 : ℚ) ^ j, j))

/-- Product terms for the shared inner kernel. -/
def centeredInnerTerms : Terms := mulTerms centeredLogTerms centeredReciprocalTerms

/-- Terms for the inner primitive, with its value at z equals negative one half subtracted. -/
def centeredHTerms : Terms :=
  (-evalTermsQ (antiTerms centeredInnerTerms) (-1 / 2), 0) :: antiTerms centeredInnerTerms

/-- Outer J1 reciprocal terms. -/
def j1WeightTerms : Terms := (List.range 10).map
  (fun j : ℕ => ((2 / 7 : ℚ) * (-2 / 7 : ℚ) ^ j, j))

/-- Outer J2 reciprocal terms. -/
def j2WeightTerms : Terms := (List.range 20).map
  (fun j : ℕ => ((2 / 15 : ℚ) * (2 / 3 : ℚ) ^ j, j)) ++ (List.range 10).map
  (fun j : ℕ => ((2 / 35 : ℚ) * (-2 / 7 : ℚ) ^ j, j))

/-- Exact rational J1 polynomial mass. -/
def j1MassQ : ℚ := massTerms (mulTerms centeredHTerms j1WeightTerms) (-1 / 2) (1 / 2)

/-- Exact rational J2 polynomial mass. -/
def j2MassQ : ℚ := massTerms (mulTerms ((1, 0) :: centeredHTerms) j2WeightTerms) (-1 / 2) (1 / 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The first rational mass certificate. -/
theorem j1MassQ_bounds : (0.01488633 : ℚ) ≤ j1MassQ ∧ j1MassQ ≤ (0.01488637 : ℚ) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The second rational mass certificate. -/
theorem j2MassQ_bounds : (0.20807491 : ℚ) ≤ j2MassQ ∧ j2MassQ ≤ (0.20807495 : ℚ) := by
  decide +kernel

end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.j1MassQ_bounds
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2MassQ_bounds
