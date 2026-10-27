/-
P0009 BJS 2022: the lab's corrected Theorem 3 chain, `ChenExplicit.AT3273.chen_3273`, linked to the
prime-plus-almost-prime form of `AlmostPrimes.Statements` and to Theorem 5. Unit U-1022, run
20261019T0403Z-4324. Every result here is CONDITIONAL ON the cited inputs named in its hypotheses;
none is an unconditional theorem. AI-written Lean code, Claude. Checked only by the Lean kernel.
Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT3273
import LeanLab.ChenExplicit.Reductions
import LeanLab.AlmostPrimes.BJSThm5At3273

open Real

namespace LeanLab.AlmostPrimes.Thm5Chain

open LeanLab.ChenExplicit LeanLab.ChenExplicit.AT3273

/-- Unconditional link: the lab's `ChenAbove T` gives the prime-plus-`Ω ≤ 2` form above `T`. -/
theorem primePlus_of_chenAbove {T : ℝ} (h : ChenAbove T) :
    ∀ N : ℕ, Even N → T < N → PrimePlusAlmostPrime 2 N := by
  intro N hE hT
  obtain ⟨p, m, hp, hN, hm0, hΩ⟩ := h N hE hT
  exact ⟨p, m, hp, Nat.pos_of_ne_zero hm0, hN, by rw [bigOmega_eq_cardFactors]; exact hΩ⟩

/-- Unconditional link: the counting form at threshold `t` gives the representation form. -/
theorem primePlus_of_BJS3At {t : ℝ} (h : BJS3At t) :
    ∀ N : ℕ, Even N → Real.exp (Real.exp t) < N → PrimePlusAlmostPrime 2 N :=
  primePlus_of_chenAbove (chenAbove_of_count (2 / 10000) (by norm_num) h)

/-- `bjs_chen_3273`'s statement, CONDITIONAL ON BJS Theorems 44, 50, 51 as corrected per
F-0020 to F-0022, through `chen_3273`. -/
theorem bjs_chen_3273_of (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (3273 / 100) (cA3273 caseA w)) (hQ : Thm50At (3273 / 100) (cQ3273 caseA))
    (hB : Thm51At (3273 / 100) cB3273) :
    ∀ N : ℕ, Even N → Real.exp (Real.exp 32.73) < N → PrimePlusAlmostPrime 2 N := by
  have := primePlus_of_BJS3At (chen_3273 caseA w hw hA hQ hB)
  intro N hE hN
  exact this N hE (by norm_num at hN ⊢; exact hN)

/-- BJS Theorem 5, every even `N ≥ 4` is a prime plus a product of at most `e^29.3` primes,
CONDITIONAL ON the corrected BJS Theorems 44, 50, 51, Dudek's theorem, Dusart Theorem 5.2 k = 2
and Dusart's `π(x) ≤ x/(ln x − 1.1)`. -/
theorem bjs_thm5_of_sieve (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (3273 / 100) (cA3273 caseA w)) (hQ : Thm50At (3273 / 100) (cQ3273 caseA))
    (hB : Thm51At (3273 / 100) cB3273) (hDu : Thm5.DudekSqfree)
    (hD : LeanLab.Common.ThetaWindow.DusartThm52k2) (hP : Thm5.DusartPi11) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ Real.exp 29.3 ∧ PrimePlusAlmostPrime k N :=
  Thm5.bjs_thm5_of_3273 (bjs_chen_3273_of caseA w hw hA hQ hB) hDu hD hP

end LeanLab.AlmostPrimes.Thm5Chain
