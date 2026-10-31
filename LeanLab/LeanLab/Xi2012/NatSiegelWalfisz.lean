import LeanLab.Xi2012.NatEncoding
import LeanLab.PNTPort.PsiChi.XiSW

/-!
Xi 2012 equation 3 for all primes with the explicit natural congruence.
The analytic chain is PsiChi.siegelWalfisz followed by PsiChi.xi_siegelWalfisz.
The latter converts the von Mangoldt sum to its prime part and handles all
nonnegative cutoffs. No theorem of the withdrawn Xi paper is an input.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

/-- Equation 3 holds for all primes with density 1. -/
theorem siegelWalfiszNat_primes :
    SiegelWalfiszNat primesUpTo (fun _ => 1) :=
  (encoding_compatibility.1 primesUpTo (fun _ => 1)).2
    LeanLab.PNTPort.PsiChi.xi_siegelWalfisz

/-- A concrete admissible family for every positive density exponent. -/
theorem primes_admissible {c₀ : ℝ} (hc₀ : 0 < c₀) :
    IsPrimeFamily primesUpTo ∧ DensityFloor (fun _ => 1) c₀ ∧
      SiegelWalfiszNat primesUpTo (fun _ => 1) :=
  ⟨primesUpTo_family, densityFloor_one hc₀, siegelWalfiszNat_primes⟩

end LeanLab.Xi2012.NatEncoding
