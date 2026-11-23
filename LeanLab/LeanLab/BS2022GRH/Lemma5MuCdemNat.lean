/-
AI wrote this Lean code, ROUTE BURST S63 wave 2, burst-20261122, unit lemma5_mu-p2.
Cohen, Dress, El Marraki 2007, Funct. Approx. Comment. Math. 37.1, 51 to 63, page 61,
Theoreme 3 bis: |R(x)| <= 0.02767 sqrt x for x >= 438653, R(x) = Q(x) - 6 x / pi^2.
The real variable leaf cdem07_thm3 of Lemma5MuS63 is FALSE as stated: at x = 441352.99,
Q(x) = 268292 and 6x/pi^2 - Q(x) > 0.02767 sqrt x, checked with exact rationals.
This file states the integer form as a LEAF, which agrees with a check to 10^7,
and proves the bridge to the upper half that journal Lemma 5 needs.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuS63

namespace LeanLab.BS2022GRH.Lemma5MuCdemNat
open Real Finset LeanLab.BS2022GRH.Lemma5MuS63

/-- LEAF: CDEM07 Theoreme 3 bis page 61, restricted to integers n ≥ 438653:
|Q(n) - 6 n / pi^2| ≤ 0.02767 sqrt n. Class HARD, cited analytic and computational input.
Checked numerically for 438653 ≤ n ≤ 10^7 in this unit, maximum ratio 0.026857 at n = 441352. -/
theorem cdem07_thm3bis_nat : ∀ n : ℕ, 438653 ≤ n →
    |(((Icc 1 n).filter (fun m => Squarefree m)).card : ℝ) - 6 / π ^ 2 * n|
      ≤ 0.02767 * √(n : ℝ) := by
  sorry

/-- PROVED from the leaf: the upper half for real x ≥ 438653. -/
theorem cdem07_upper_real (x : ℝ) (hx : 438653 ≤ x) :
    (((Icc 1 ⌊x⌋₊).filter (fun m => Squarefree m)).card : ℝ) - 6 / π ^ 2 * x
      ≤ 0.02767 * √x := by
  have hn : 438653 ≤ ⌊x⌋₊ := by
    rw [Nat.le_floor_iff (by linarith)]; exact_mod_cast hx
  have hA := (abs_le.1 (cdem07_thm3bis_nat _ hn)).2
  have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h3 : √(⌊x⌋₊ : ℝ) ≤ √x := Real.sqrt_le_sqrt h2
  have h4 : 0 ≤ 6 / π ^ 2 := by positivity
  nlinarith

/-- Buthe 2014 display 4.6 upper half as journal Lemma 5 uses it, assembled from the
integer leaf above and the middle range leaf of Lemma5MuS63. CONDITIONAL ON those leaves. -/
theorem lemma5_mu_assembled_nat : PaperInputs148.Lemma5MuJ := by
  intro x hx
  rcases lt_or_ge x (K0 + 1) with h | h
  · exact lemma5_mu_small x hx h
  rcases lt_or_ge x 438653 with h' | h'
  · exact buthe_compute_mid x h h'
  · have hA := cdem07_upper_real x h'
    rw [mMu_mul x (by linarith)]
    have hs : 0 ≤ √x := Real.sqrt_nonneg _
    linarith

end LeanLab.BS2022GRH.Lemma5MuCdemNat

#print axioms LeanLab.BS2022GRH.Lemma5MuCdemNat.cdem07_upper_real
#print axioms LeanLab.BS2022GRH.Lemma5MuCdemNat.lemma5_mu_assembled_nat
