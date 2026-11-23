/-
Burst burst-20261122, session S78, target LiuWang2002. A shorter route for the cited input
`U1543.rs2_mertens` of Decomp1543b.lean, Liu-Wang 2002 p. 172: for `x ≥ 15000`,
`log x - 1.385 ≤ Σ_{p≤x} log p / p ≤ log x - 1.28`.
RSMertens1122 splits it along Rosser-Schoenfeld 1962 p. 87 into four LEAFs. Here the theta
window `G_window` of RSMertens1122 is run on the whole range `[15000, 10^10]` with
J. Büthe, An analytic method for bounding ψ(x), Math. Comp. 87, 2018, arXiv 1511.02032v2,
p. 2 Theorem 2, displays (1.6) and (1.7), read on the rendered page:
(1.6) `x - θ(x) ≤ 1.95 √x` for `1423 ≤ x ≤ 10^19`; (1.7) `x - θ(x) > 0.05 √x` for
`1 ≤ x ≤ 10^19`. Display (1.7) is the lab's existing LEAF
`BS2022GRH.ThetaInputs224.theta_buthe_1e19`, reused, not restated.
This drops RS Theorem 18 and RS Theorem 6 on `[10^8, 10^10]` from the route: the named
inputs become (1.6), (1.7), the value at 15000 and the Dusart row.
AI-written Lean code, Claude, 2026-11-22. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LiuWang2002.RSMertens1122
import LeanLab.BS2022GRH.ThetaInputs224

open Real Finset

noncomputable section
namespace LeanLab.LiuWang2002.RSMertensButhe1122

open LeanLab.AlmostPrimes.MertensRS320 (R)
open LeanLab.Common.ThetaWindow (DusartThm52k2)
open LeanLab.LiuWang2002.RSMertens1122

/-- **Assembly**, CONDITIONAL ON the named inputs `h16`, `h17`, `h15000`, `hD`: the statement
of `U1543.rs2_mertens`. On `[15000, 10^10]` by `G_window` with `K = 1.95` from Büthe (1.6) and
`R ≤ 0` from Büthe (1.7); above `10^10` by `G_diff_dusart` from the value at `10^10`. -/
theorem rs2_mertens_of_buthe
    (h16 : ∀ x : ℝ, 1423 ≤ x → x ≤ 10 ^ 19 → x - Chebyshev.theta x ≤ 1.95 * √x)
    (h17 : ∀ x : ℝ, 1 ≤ x → x ≤ 1e19 → (0.05 : ℝ) * √x < x - Chebyshev.theta x)
    (h15000 : -1.35 ≤ (∑ p ∈ (range (⌊(15000 : ℝ)⌋₊ + 1)).filter Nat.Prime,
        Real.log p / p) - Real.log 15000 ∧
      (∑ p ∈ (range (⌊(15000 : ℝ)⌋₊ + 1)).filter Nat.Prime, Real.log p / p) -
        Real.log 15000 ≤ -1.30)
    (hD : DusartThm52k2) (x : ℝ) (hx : 15000 ≤ x) :
    Real.log x - 1.385 ≤ ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ∧
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ≤ Real.log x - 1.28 := by
  have h122 : (122 : ℝ) ≤ √15000 := by
    rw [show (122 : ℝ) = √(122 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hK1 : 1.95 / √15000 ≤ 1.95 / 122 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h122
  have hK2 : 2 * 1.95 / √15000 ≤ 2 * 1.95 / 122 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h122
  have n1 : (2 * 1.95 / 122 : ℝ) ≤ 0.032 := by norm_num
  have n2 : (1.95 / 122 : ℝ) ≤ 0.016 := by norm_num
  obtain ⟨l0, u0⟩ := h15000
  -- the window on `[15000, y]` for `y ≤ 10^10`
  have hwin : ∀ y : ℝ, 15000 ≤ y → y ≤ 10 ^ 10 →
      -1.382 ≤ (∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log y ∧
      (∑ p ∈ (range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.log p / p) - Real.log y ≤ -1.284 := by
    intro y hy hy10
    obtain ⟨lW, uW⟩ := G_window (a := 15000) (b := y) (K := 1.95) (by norm_num) hy
      (by norm_num) (fun t ht => by
        have ht1 : 15000 ≤ t := ht.1
        have ht2 : t ≤ 10 ^ 10 := le_trans ht.2 hy10
        have a := h16 t (by linarith) (by linarith)
        have b := h17 t (by linarith) (by norm_num at ht2 ⊢; linarith)
        have hs : 0 ≤ √t := Real.sqrt_nonneg t
        constructor <;> simp only [R] <;> nlinarith)
    constructor <;> linarith
  rcases le_or_gt x (10 ^ 10) with hx10 | hx10
  · obtain ⟨l, u⟩ := hwin x hx hx10
    constructor <;> linarith
  · obtain ⟨l, u⟩ := hwin (10 ^ 10) (by norm_num) le_rfl
    have hd := G_diff_dusart hD (le_refl (10 ^ 10 : ℝ)) hx10.le
    rw [abs_le] at hd
    obtain ⟨dl, du⟩ := hd
    constructor <;> linarith

/-- LEAF: Büthe 2018, arXiv 1511.02032v2, p. 2 Theorem 2 display (1.6):
`x - θ(x) ≤ 1.95 √x` for `1423 ≤ x ≤ 10^19`. Established by the paper's analytic method with
the zeros up to height 10^11. Class HARD, cited wall. -/
theorem buthe2018_16 (x : ℝ) (hx : 1423 ≤ x) (hx19 : x ≤ 10 ^ 19) :
    x - Chebyshev.theta x ≤ 1.95 * √x := by
  sorry

/-- The statement of `U1543.rs2_mertens`, Liu-Wang p. 172, from Büthe (1.6) above, the lab's
Büthe (1.7) LEAF, and the RSMertens1122 LEAFs `rs1962_thm21_at_15000`, `dusart_thm52_k2`. -/
theorem rs2_mertens_buthe (x : ℝ) (hx : 15000 ≤ x) :
    Real.log x - 1.385 ≤ ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ∧
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p / p ≤ Real.log x - 1.28 :=
  rs2_mertens_of_buthe buthe2018_16 LeanLab.BS2022GRH.ThetaInputs224.theta_buthe_1e19
    rs1962_thm21_at_15000 dusart_thm52_k2 x hx

end LeanLab.LiuWang2002.RSMertensButhe1122
