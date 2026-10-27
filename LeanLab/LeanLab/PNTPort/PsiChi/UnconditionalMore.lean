import LeanLab.PNTPort.PsiChi.SiegelWalfisz
import LeanLab.HeathBrown1985.RightOrderUpper
import LeanLab.HeathBrown1985.Bound24
import LeanLab.HeathBrown1985.Vinogradov
import LeanLab.HeathBrown1985.ManyReps

/-!
# More of the lab's Siegel-Walfisz consequences, now unconditional

Lab proof, unit U-1040, PC run 20261019T0703Z-249. AI wrote the Lean code. Each theorem applies
an existing lab deduction `*_of_siegelWalfisz`, until now CONDITIONAL ON `SiegelWalfisz`, to the
cloud's `siegelWalfisz` of U-5209, rebuilt independently in U-1038. Known mathematics,
ineffective constants. Binary Goldbach is OPEN: every result here is an almost-all statement.

* `heathBrown_theorem2`: Heath-Brown 1985 Theorem 2, the mean square of `ψ(x; k, l) - x/φ(k)`
  over `k ≤ x (log x)^{-C}`;
* `heathBrown_corollary2`: every large odd number is a sum of three primes, as a natural bound;
* `goldbach_hardyLittlewood_almostAll`: for every `ε > 0` and `C > 0`, all but
  `O(X (log X)^{-C})` even `m ≤ X` satisfy
  `(1 - ε) 𝔖(m) m / log² m ≤ r(m) ≤ (1 + ε) 𝔖(m) m / log² m`, with `r(m)` the ordered count
  of prime pairs: the Hardy-Littlewood asymptotic for almost all even `m`;
* `goldbach_rightOrder`: the upper bound `r(m) ≪ m / log² m ∏_{p ∣ m} (1 + 1/p)` for every `m`,
  and few `m` with `r(m) < (13/240) m / log² m`;
* `fewReps_card`: Heath-Brown's few representations count.
-/

open Real Finset

namespace LeanLab.PNTPort.PsiChi
open LeanLab.HeathBrown1985

theorem heathBrown_theorem2 : HeathBrown1985.Theorem2 :=
  theorem2_of_siegelWalfisz siegelWalfisz

theorem heathBrown_corollary2 : HeathBrown1985.Corollary2 :=
  corollary2_of_siegelWalfisz siegelWalfisz

/-- **Hardy-Littlewood for almost all even `m`**, unconditional, ineffective. -/
theorem goldbach_hardyLittlewood_almostAll {ε : ℝ} (hε : 0 < ε) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X →
      (((range (⌊X⌋₊ + 1)).filter (fun m => Even m ∧ 4 ≤ m ∧
        ¬ ((1 - ε) * singular m * m / Real.log m ^ 2 ≤ (LeanLab.SchnirelmannGoldbach.r m : ℝ) ∧
           (LeanLab.SchnirelmannGoldbach.r m : ℝ) ≤ (1 + ε) * singular m * m / Real.log m ^ 2))).card : ℝ)
        ≤ K * X * Real.log X ^ (-C) :=
  rightOrderAsymptotic_of_siegelWalfisz siegelWalfisz hε C hC

theorem goldbach_rightOrder :
    (∃ C' : ℝ, ∀ m : ℕ, 3 ≤ m →
      (LeanLab.SchnirelmannGoldbach.r m : ℝ) ≤
        C' * m / Real.log m ^ 2 * LeanLab.SchnirelmannGoldbach.singProd m) ∧
    (∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X →
      ((lowUpToc (13 / 240) X).card : ℝ) ≤ K * X * Real.log X ^ (-C)) :=
  rightOrderSharp_of_siegelWalfisz siegelWalfisz

theorem fewReps_card (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → ((fewReps x).card : ℝ) ≤ K * x * Real.log x ^ (-C) :=
  fewReps_card_of_siegelWalfisz siegelWalfisz C hC

end LeanLab.PNTPort.PsiChi
