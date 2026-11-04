/- AI wrote this Lean code for CODEX task233.
Unchanged shared definitions moved for the Theorem 5 proof. Goldbach is open. -/
import LeanLab.BS2022GRH.ChenThresholdGRH

namespace LeanLab.BS2022GRH.DecompC169a
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- The primes in P below x, journal p. 1227. -/
def primesBelow (n : ℕ) (x : ℝ) : Finset ℕ :=
  (range ⌈x⌉₊).filter (fun p => p.Prime ∧ ¬ p ∣ n ∧ (p : ℝ) < x)

/-- The small prime product Q in the proof of Theorem 5, p. 1229. -/
def smallProduct (n : ℕ) (u : ℝ) : ℕ := ∏ p ∈ primesBelow n u, p

/-- The density V at z, journal pp. 1227 and 1229. -/
def density (n : ℕ) : ℝ :=
  ∏ p ∈ primesBelow n (U7153.zz n), (1 - 1 / ((p : ℝ) - 1))

/-- The residue error r of Theorem 5, journal p. 1229. -/
def residue (n d : ℕ) : ℝ :=
  (((U7153.Aset n).filter (fun a => d ∣ a)).card : ℝ) -
    ((U7153.Aset n).card : ℝ) / (d.totient : ℝ)

/-- The squarefree divisors d of P at z with d less than QD, p. 1229. -/
def sieveDivisors (n : ℕ) (α u : ℝ) : Finset ℕ :=
  ((primesBelow n (U7153.zz n)).powerset.image (fun T => ∏ p ∈ T, p)).filter
    (fun d => (d : ℝ) < smallProduct n u * (n : ℝ) ^ (1 / 2 - α))

/-- The sum of absolute residue errors in the lower sieve, p. 1229. -/
def remainder (n : ℕ) (α u : ℝ) : ℝ :=
  ∑ d ∈ sieveDivisors n α u, |residue n d|

/-- The lower sieve coefficient at s equal to 4 minus 8 alpha, p. 1229. -/
def lowerCoefficient (α ε C₂ : ℝ) : ℝ :=
  2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α) -
    ε * C₂ * (3 * exp (8 * α - 2) / (4 - 8 * α))

/-- The main term before bounding V and the cardinality, p. 1229. -/
def sieveMain (n : ℕ) (α ε C₂ : ℝ) : ℝ :=
  lowerCoefficient α ε C₂ * density n * ((U7153.Aset n).card : ℝ)

end
end LeanLab.BS2022GRH.DecompC169a
