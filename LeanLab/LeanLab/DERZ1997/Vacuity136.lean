/-
Concrete instances for the statements completed by CODEX task136.
P0011 page 100 supplies the Fourier and weighted-count normalization.
The kernel instances follow Davenport chapter 17, page 105.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.DERZ1997.Decomp136
import LeanLab.DERZ1997.Decomp136b
import LeanLab.DERZ1997.Decomp1529c
open LeanLab.DERZ1997.Decomp136 LeanLab.DERZ1997.Decomp136b
open LeanLab.DERZ1997.Decomp1529a LeanLab.DERZ1997.Decomp1529b LeanLab.DERZ1997.Decomp1529c
open LeanLab.DERZ1997.Perron136
#print axioms LeanLab.DERZ1997.Decomp1529b.perronI
example : (∫ α : ℝ in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * (-1 : ℤ))) = 0 := by
  simpa using fourier_orthogonality (-1)
example : (3, 3, 3) ∈ primeTriples 9 := by
  rw [mem_primeTriples]
  norm_num
example : 0 < weightedJ 9 := by
  apply (weightedJ_pos_iff_nonempty 9).mpr
  refine ⟨(3, 3, 3), ?_⟩
  rw [mem_primeTriples]
  norm_num
example : Real.exp 1 ≤ (3 : ℝ) ∧ (zetaZerosWindow 3).Finite := by
  constructor
  · linarith [Real.exp_one_lt_d9]
  · apply (zetaZeros_finite 4).subset
    intro z hz
    refine ⟨hz.1, hz.2.1, hz.2.2.1, ?_⟩
    rw [abs_of_pos (by linarith [hz.2.2.2.1])]
    linarith [hz.2.2.2.2]
example : (LZeros (1 : DirichletCharacter ℂ 5) 15).Finite := LZeros_finite _ _
example : ‖gaussSum (1 : DirichletCharacter ℂ 4) ZMod.stdAddChar‖ ≤ Real.sqrt (4 : ℝ) := by
  simpa using gaussSum_norm_le (q := 4) (1 : DirichletCharacter ℂ 4)
example : gaussSum (1 : DirichletCharacter ℂ 4) ZMod.stdAddChar = (ArithmeticFunction.moebius 4 : ℂ) :=
  gaussSum_one
example : ‖perronI (1/2) 1 1‖ ≤ (1/2 : ℝ) ^ (1 : ℝ) * min 1 (1 / ((1 : ℝ) * |Real.log (1/2)|)) :=
  perron_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : ‖perronI 2 1 1 - 1‖ ≤ (2 : ℝ) ^ (1 : ℝ) * min 1 (1 / ((1 : ℝ) * Real.log 2)) :=
  perron_gt_one (by norm_num) (by norm_num) (by norm_num)
example : ‖perronI 1 1 1 - 1/2‖ ≤ (1 : ℝ) / 1 := perron_one (by norm_num) (by norm_num)
example : ‖perronI 1 1 1‖ ≤ (1 : ℝ) ^ (1 : ℝ) :=
  perron_norm_small (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * ((2 : ℝ) / n) ^ (2 : ℝ)) :=
  perron_coeff_summable (by norm_num) (by norm_num)
