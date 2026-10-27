import Mathlib
import LeanLab.Zhao2025.Zhao2025U6825Lemma31
import LeanLab.Zhao2025.Zhao2025U6841G
import LeanLab.Zhao2025.Zhao2025U6841N0

/-!
# Zhao 2025, the R input `r₃ ≤ 0.25` of layout C at `λ* = 0.74`, `Λ = 1.363`, `N* = 3`

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6841, CLOUD 20261021T0316Z-cloud57.
AI wrote the Lean code.  Binary Goldbach is open.

The bound of (3.42), (3.43) with `λ₁ = λ₂ = λ* = λ₀ = 0.74`, `M = O(1)`, `N* = 3`, at
`x = 1.361`, in the form of numerics/zhao_U6837_R.py `Rbound`:
`max(r343, 2E + (N*-2)E)`, `E = e^{-Wλ*} - e^{-WΛ}`, `ψ = G(z₂)/G(z₁)`, `ψ* = G(0)/G(z₁)`,
`Δ = ψ - (ϕ/2) x g(0)/G(z₁)`, `Dmax = (1 - (N*+1)Δ²)/(2Δ)`,
`r343 = 2E + E/(ψ* - ψ) · max(Dmax - 2(ψ* - ψ), 0)`.
Python `r343 = 0.248875`, `(3.42)` branch `0.222688`.  Proved: the formula is at most `0.25`.
The (3.43) display itself was read from the page image in U-6837; the definition `r3val`
transcribes the lab script, a faithfulness point to recheck against p. 8 of the arXiv PDF.
-/

namespace LeanLab.Zhao2025.U6841

open LeanLab.Pintz2018 LeanLab.Zhao2025.U6825

/-- The (3.42), (3.43) value with `λ₁ = λ₂ = λ* = λ₀ = l`, `N* = 3`, `W = 10/3`. -/
noncomputable def r3val (x L l : ℝ) : ℝ :=
  let E := Real.exp (-(10 / 3 * l)) - Real.exp (-(10 / 3 * L))
  let G1 := Gz (-l / x)
  let psi := Gz ((L - l) / x) / G1
  let psis := Gz 0 / G1
  let D := psi - 1 / 6 * x * (16 / 15) / G1
  let Dmax := (1 - 4 * D ^ 2) / (2 * D)
  max (2 * E + E / (psis - psi) * max (Dmax - 2 * (psis - psi)) 0) (2 * E + (3 - 2) * E)

theorem ya : 0.3370797569 ≤ Real.exp (-(1480 / 1361)) ∧ Real.exp (-(1480 / 1361)) ≤ 0.3370797570 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem yb : 0.4003150942 ≤ Real.exp (-(1246 / 1361)) ∧ Real.exp (-(1246 / 1361)) ≤ 0.4003150943 :=
  ⟨eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num),
   eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)⟩

theorem yc : Real.exp (-(37 / 15)) ≤ 0.0848672790 :=
  eb_up _ _ (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)

theorem yd : 0.0106378877 ≤ Real.exp (-(1363 / 300)) :=
  eb_lo _ _ (by norm_num) (by norm_num) (by simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)

theorem H1_bounds : 1.2005 ≤ Gz (-(74 / 136.1)) ∧ Gz (-(74 / 136.1)) ≤ 1.2007 := by
  have e0 : -((74 : ℝ) / 136.1) = -740 / 1361 := by norm_num
  rw [e0]
  have h := G_closed (-740 / 1361) (by norm_num)
  have e : -(2 * (-740 / 1361 : ℝ)) = 1480 / 1361 := by norm_num
  rw [e] at h
  have hm : Real.exp (1480 / 1361) * Real.exp (-(1480 / 1361)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (1480 / 1361)
  obtain ⟨a1, a2⟩ := ya
  have l1 : 2.96665 ≤ Real.exp (1480 / 1361) := by nlinarith
  have l2 : Real.exp (1480 / 1361) ≤ 2.96668 := by nlinarith
  unfold Gz; rw [h]; norm_num
  constructor <;> nlinarith

theorem H2_bounds : 0.7120 ≤ Gz (62.3 / 136.1) ∧ Gz (62.3 / 136.1) ≤ 0.7122 := by
  have e0 : (62.3 : ℝ) / 136.1 = 623 / 1361 := by norm_num
  rw [e0]
  have h := G_closed (623 / 1361) (by norm_num)
  have e : -(2 * (623 / 1361 : ℝ)) = -(1246 / 1361) := by norm_num
  rw [e] at h
  obtain ⟨b1, b2⟩ := yb
  unfold Gz; rw [h]; norm_num
  constructor <;> nlinarith

/-- PROVED unconditional: the (3.42), (3.43) value at `x = 1.361`, `Λ = 1.363`, `λ* = 0.74`,
`N* = 3` is at most `0.25`; the layout C input `r₃`, Python `0.24888`. -/
theorem r3_le : r3val 1.361 1.363 0.74 ≤ 0.25 := by
  have g0 : Gz 0 = 8 / 9 := G_zero
  have e1 : -(0.74 : ℝ) / 1.361 = -(74 / 136.1) := by norm_num
  have e2 : ((1.363 : ℝ) - 0.74) / 1.361 = 62.3 / 136.1 := by norm_num
  have e3 : -(10 / 3 * (0.74 : ℝ)) = -(37 / 15) := by norm_num
  have e4 : -(10 / 3 * (1.363 : ℝ)) = -(1363 / 300) := by norm_num
  unfold r3val
  simp only [e1, e2, e3, e4, g0]
  obtain ⟨g1, g2⟩ := H1_bounds
  obtain ⟨h1, h2⟩ := H2_bounds
  set G1 := Gz (-(74 / 136.1))
  set G2 := Gz (62.3 / 136.1)
  set E := Real.exp (-(37 / 15)) - Real.exp (-(1363 / 300)) with hE
  have hE1 : E ≤ 0.0742294 := by have := yc; have := yd; rw [hE]; linarith
  have hE0 : 0 ≤ E := by
    rw [hE, sub_nonneg]; exact Real.exp_le_exp.mpr (by norm_num)
  have hG1 : 0 < G1 := by linarith
  set D := G2 / G1 - 1 / 6 * 1.361 * (16 / 15) / G1 with hDdef
  have hD : 0.3914 ≤ D := by
    rw [hDdef, ← sub_div, le_div_iff₀ hG1]; nlinarith
  set s := 8 / 9 / G1 - G2 / G1 with hsdef
  have hs : 0.1471 ≤ s := by
    rw [hsdef, ← sub_div, le_div_iff₀ hG1]; nlinarith
  have hDmax : (1 - 4 * D ^ 2) / (2 * D) ≤ 0.4950 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hmx : max ((1 - 4 * D ^ 2) / (2 * D) - 2 * s) 0 ≤ 0.2008 :=
    max_le (by linarith) (by norm_num)
  have hmx0 : 0 ≤ max ((1 - 4 * D ^ 2) / (2 * D) - 2 * s) 0 := le_max_right _ _
  have hEs : E / s ≤ 0.0742294 / 0.1471 := by
    calc E / s ≤ 0.0742294 / s := by gcongr
      _ ≤ 0.0742294 / 0.1471 := by gcongr
  have hEs0 : 0 ≤ E / s := div_nonneg hE0 (by linarith)
  apply max_le
  · have := mul_le_mul hEs hmx hmx0 (by norm_num)
    nlinarith
  · linarith

end LeanLab.Zhao2025.U6841

#print axioms LeanLab.Zhao2025.U6841.H1_bounds
#print axioms LeanLab.Zhao2025.U6841.H2_bounds
#print axioms LeanLab.Zhao2025.U6841.r3_le
