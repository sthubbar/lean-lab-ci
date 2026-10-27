/-
P0045 Languasco, Pintz, Zaccagnini 2007: where the repaired chain now stands.

Unit U-1229, T1, PC run 20261020T1203Z-6833.

* `few_Rpp_zero_of_eq25`: almost every even `N ∈ J(X)` has `R''_k(N) > 0`, so is a sum of two prime
  powers and `k` powers of two, with at most `B X^{3/5} (log X)^{10}` exceptions, CONDITIONAL ON the
  repaired (25), `Eq25C (2c₀ C(k, N))`, ONLY. Every other input of the chain is PROVED in the lab:
  (3) `eq3_proved`, the minor arc bound `minorBound_proved`, (7) `eq7_proved`, Lemma 6.1
  `Lemma61Port.lemma61_proved`, `2c₀ > 0`.

KNOWN mathematics. AI wrote this Lean code. Checked only by the Lean kernel.
Binary Goldbach is OPEN; nothing here is Goldbach.
-/
import Mathlib
import LeanLab.LPZ2007.MinorBoundProof
import LeanLab.LPZ2007.Lemma61Port
import LeanLab.LPZ2007.FewRppRepaired

namespace LeanLab.LPZ2007.Corollary

open Finset LeanLab.LPZ2007

open Classical in
/-- **P0045's corollary on the repaired constant, CONDITIONAL ON the repaired (25) only.** -/
theorem few_Rpp_zero_of_eq25 (h25 : Eq25C (fun k N => twoC0 * Ckn k N)) {k : ℕ} (hk : 1 ≤ k) :
    ∃ B : ℝ, 0 < B ∧ ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      (((Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧ InJ X N ∧ Rpp k X N ≤ 0)).card : ℝ) ≤
        B * X ^ (3 / 5 : ℝ) * Real.log X ^ 10 :=
  few_Rpp_zero_twoC0 (MinorBoundProof.mainJ_twoC0_of_eq25 h25) Lemma61Port.lemma61_proved hk

/-- `C(k, N)` lies in `[1, Σ' f(d)/ξ(d)]`, now with Lemma 6.1 PROVED. -/
theorem Ckn_bounds (j N : ℕ) :
    1 ≤ Ckn (j + 1) N ∧ Ckn (j + 1) N ≤ ∑' d, romanovTerm d :=
  ⟨one_le_Ckn Lemma61Port.lemma61_proved j N, Ckn_le_romanov Lemma61Port.lemma61_proved j N⟩

end LeanLab.LPZ2007.Corollary
