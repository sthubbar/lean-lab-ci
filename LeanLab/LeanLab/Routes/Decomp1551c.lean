/-
Unit U-1551, track T1, DECOMPOSE, run 20261026T1219Z-15327, 2026-10-26. PALOMAR line I5171.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Decomposition of the input `SmoothT2.Ordinates14 gZ` of
`LeanLab.Routes.U1508.goldbach_445_hsw_gZ` under RH: every nontrivial zero of ζ has
`|Im ρ| ≥ 14`. Under RH a zero is `1/2 + iγ`; by `riemannZeta_conj` one may take `γ ≥ 0`; so it
suffices that `ζ(1/2 + it) ≠ 0` for `0 ≤ t < 14`. This follows from the Euler-Maclaurin
approximant `EM10` with `N = 10` and two Bernoulli corrections, Edwards, Riemann's Zeta
Function 1974, section 6.4: its remainder is below `1/100` on the segment, LEAVES
`em10_remainder` and `rem_small`, while `‖EM10(1/2 + it)‖ ≥ 1/20` on `[0, 14]`, LEAVES
`em10_lower_a`, `em10_lower_b`, `em10_lower_c`, a finite certified computation. A float check
with mpmath at 30 digits on a grid of step 0.001 gives the minimum `0.1056` at `t = 14`, and
the remainder bound `0.0051` at `t = 14`.

ASSEMBLY `ordinates14_gZ_of_RH`, CONDITIONAL ON the five leaves.
-/
import Mathlib
import LeanLab.PNTPort.ExplicitPsi1.DudekTrudgian
import LeanLab.ChirreHagen2025.SmoothTheorem2

namespace LeanLab.Routes.Decomp1551c

open Complex
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx re_half_of_RH)

local notation "ζ" => riemannZeta

/-- The Euler-Maclaurin approximant of `ζ(s)` with `N = 10` and the Bernoulli terms `B₂`, `B₄`:
`Σ_{n<10} n^{-s} + 10^{1-s}/(s-1) + 10^{-s}/2 + s 10^{-s-1}/12 - s(s+1)(s+2) 10^{-s-3}/720`. -/
noncomputable def EM10 (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Ico (1 : ℕ) 10, ((n : ℕ) : ℂ) ^ (-s)) + (10 : ℂ) ^ (1 - s) / (s - 1) + (10 : ℂ) ^ (-s) / 2
    + s * (10 : ℂ) ^ (-s - 1) / 12 - s * (s + 1) * (s + 2) * (10 : ℂ) ^ (-s - 3) / 720

/-- LEAF. Unit U-1551. Edwards 1974, section 6.4, Euler-Maclaurin summation for `ζ` with
`N = 10` and `m = 2`: the remainder `-s(s+1)(s+2)(s+3)/4! ∫_N^∞ B̃₄(x) x^{-s-4} dx`, with
`|B̃₄| ≤ 1/30`, satisfies `|ζ(s) - EM10(s)| ≤ |s(s+1)(s+2)(s+3)| 10^{-σ-3} / (720 (σ+3))`
for `σ = Re s > 0`, `s ≠ 1`. The lab's port `PNTPort/StrongPNT/EulerMaclaurin.lean` has the
first-order summation formula. -/
theorem em10_remainder (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖ζ s - EM10 s‖ ≤
      ‖s * (s + 1) * (s + 2) * (s + 3)‖ * (10 : ℝ) ^ (-(s.re + 3)) / (720 * (s.re + 3)) := by
  sorry

/-- LEAF. Unit U-1551. Arithmetic for the remainder of `em10_remainder` on the half line
segment: for `s = 1/2 + it`, `0 ≤ t ≤ 14`,
`|s(s+1)(s+2)(s+3)| 10^{-7/2} / (720 · 7/2) ≤ 1/100`; at `t = 14` the left side is `0.0051`. -/
theorem rem_small (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 14) :
    ‖((1 / 2 : ℂ) + t * I) * ((1 / 2 : ℂ) + t * I + 1) * ((1 / 2 : ℂ) + t * I + 2) *
        ((1 / 2 : ℂ) + t * I + 3)‖ * (10 : ℝ) ^ (-((1 / 2 : ℝ) + 3)) / (720 * ((1 / 2 : ℝ) + 3))
      ≤ 1 / 100 := by
  sorry

/-- LEAF. Unit U-1551. Finite certified computation, first piece: `|EM10(1/2 + it)| ≥ 1/20`
for `0 ≤ t ≤ 7`; float minimum `0.526`. A grid with a Lipschitz bound for `EM10` suffices. -/
theorem em10_lower_a (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 7) :
    1 / 20 ≤ ‖EM10 ((1 / 2 : ℂ) + t * I)‖ := by
  sorry

/-- LEAF. Unit U-1551. Finite certified computation, second piece: `|EM10(1/2 + it)| ≥ 1/20`
for `7 ≤ t ≤ 12`; float minimum `1.0956`. -/
theorem em10_lower_b (t : ℝ) (ht0 : 7 ≤ t) (ht : t ≤ 12) :
    1 / 20 ≤ ‖EM10 ((1 / 2 : ℂ) + t * I)‖ := by
  sorry

/-- LEAF. Unit U-1551. Finite certified computation, third piece: `|EM10(1/2 + it)| ≥ 1/20`
for `12 ≤ t ≤ 14`; float minimum `0.1056` at `t = 14`, where `|ζ(1/2 + 14i)| = 0.1056`; the
first zero is at `t = 14.1347`. -/
theorem em10_lower_c (t : ℝ) (ht0 : 12 ≤ t) (ht : t ≤ 14) :
    1 / 20 ≤ ‖EM10 ((1 / 2 : ℂ) + t * I)‖ := by
  sorry

/-- `ζ(1/2 + it) ≠ 0` for `0 ≤ t ≤ 14`, CONDITIONAL ON the five leaves. -/
theorem zeta_half_ne_zero (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 14) :
    ζ ((1 / 2 : ℂ) + t * I) ≠ 0 := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hsdef
  have hre : s.re = 1 / 2 := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hR := em10_remainder s (by rw [hre]; norm_num) hs1
  rw [hre] at hR
  have hR2 := rem_small t ht0 ht
  have hL : 1 / 20 ≤ ‖EM10 s‖ := by
    rcases le_total t 7 with h7 | h7
    · exact em10_lower_a t ht0 h7
    rcases le_total t 12 with h12 | h12
    · exact em10_lower_b t h7 h12
    · exact em10_lower_c t h12 ht
  intro h0
  rw [h0, zero_sub, norm_neg] at hR
  have : ‖s * (s + 1) * (s + 2) * (s + 3)‖ * (10 : ℝ) ^ (-((1 / 2 : ℝ) + 3)) /
      (720 * ((1 / 2 : ℝ) + 3)) ≤ 1 / 100 := by simpa [hsdef] using hR2
  linarith

/-- ASSEMBLY. Under RH, every ordinate `gZ i` of a nontrivial zero of ζ has `|gZ i| ≥ 14`.
CONDITIONAL ON the leaves `em10_remainder`, `rem_small`, `em10_lower_a`, `em10_lower_b`,
`em10_lower_c`. -/
theorem ordinates14_gZ_of_RH (hRH : RiemannHypothesis) :
    LeanLab.ChirreHagen2025.SmoothT2.Ordinates14 gZ := by
  intro i
  by_contra hlt
  rw [not_le] at hlt
  have hz : ζ (i.1 : ℂ) = 0 := i.1.2.1
  have hre : ((i.1 : ℂ)).re = 1 / 2 := re_half_of_RH hRH i.1
  set g := gZ i with hg
  have hgim : ((i.1 : ℂ)).im = g := rfl
  have hrho : (i.1 : ℂ) = (1 / 2 : ℂ) + g * I := by
    apply Complex.ext <;> simp [hre, hgim]
  rcases le_total 0 g with h0 | h0
  · apply zeta_half_ne_zero g h0 (by rw [abs_of_nonneg h0] at hlt; linarith)
    rw [← hrho]; exact hz
  · apply zeta_half_ne_zero (-g) (by linarith) (by rw [abs_of_nonpos h0] at hlt; linarith)
    have hc : (1 / 2 : ℂ) + ((-g : ℝ) : ℂ) * I = (starRingEnd ℂ) (i.1 : ℂ) := by
      rw [hrho]; apply Complex.ext <;> simp
    rw [hc, riemannZeta_conj, hz, map_zero]

end LeanLab.Routes.Decomp1551c
