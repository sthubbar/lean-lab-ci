import LeanLab.ExceptionalSet.UpJ200.PrimeVaughan446
import LeanLab.ExceptionalSet.U1423MVMinor
import LeanLab.ExceptionalSet.UpJ200.TailParameters385

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.MinorSup446`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
The real prime minor supremum in P0082 page 366 after display 27.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.MinorSup446

open Real Filter Topology
open LeanLab.ExceptionalSet.U1539 (Sp calE)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp404e (truncatedDomain)

/-- P0082 page 366 after display 27. For small delta the rational Vaughan
bound and the explicit cutoff errors fit one power of X with log power 4.
This is auxiliary scalar arithmetic with explicit constant 14404. -/
theorem vaughan_scalar (X δ : ℝ) (hX : 1 ≤ X) (hL : 1 ≤ Real.log X)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 30) :
    300 * (2 * X / Real.sqrt (X ^ (6 * δ)) + X ^ (4 / 5 : ℝ)) * (1 + Real.log X) ^ 4 +
        2 * Real.sqrt X * Real.log X + Real.log 4 * X ^ (6 * δ) ≤
      14404 * X ^ (1 - 3 * δ) * Real.log X ^ 4 := by
  let V := X ^ (1 - 3 * δ)
  let L := Real.log X
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hV : 0 ≤ V := Real.rpow_nonneg hX0.le _
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL
  have hLl : L ≤ L ^ 4 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hL (by norm_num : (1 : ℕ) ≤ 4))
  have h80 : X ^ (4 / 5 : ℝ) ≤ V :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hP : X ^ (6 * δ) ≤ V :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hs : Real.sqrt X ≤ V := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hp : X / Real.sqrt (X ^ (6 * δ)) = V := by
    dsimp [V]
    rw [MV75U1423.sqrt_P X δ hX0.le, Real.rpow_sub hX0, Real.rpow_one]
  have hLp : (1 + L) ^ 4 ≤ 16 * L ^ 4 := by
    calc
      _ ≤ (2 * L) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = _ := by ring
  have hm : 300 * (2 * X / Real.sqrt (X ^ (6 * δ)) + X ^ (4 / 5 : ℝ)) * (1 + L) ^ 4 ≤
      14400 * V * L ^ 4 := by
    rw [show 2 * X / Real.sqrt (X ^ (6 * δ)) = 2 * V by rw [mul_div_assoc, hp]]
    calc
      _ ≤ 300 * (3 * V) * (16 * L ^ 4) := by gcongr; linarith
      _ = _ := by ring
  have he : 2 * Real.sqrt X * L ≤ 2 * V * L ^ 4 := by gcongr
  have hc : Real.log 4 * X ^ (6 * δ) ≤ 2 * V * L ^ 4 := by
    have hl4 : 0 ≤ Real.log 4 := (LeanLab.PNTPort.Vinogradov.log4_bounds).1
    have hl4u : Real.log 4 ≤ 2 := (LeanLab.PNTPort.Vinogradov.log4_bounds).2.le
    calc
      _ ≤ 2 * V := mul_le_mul hl4u hP (Real.rpow_nonneg hX0.le _) (by norm_num)
      _ ≤ 2 * V * L ^ 4 := le_mul_of_one_le_right (by positivity) hL4
  change _ ≤ 14404 * V * L ^ 4
  change _ ≤ _ at hm he hc
  dsimp only [L] at hm he hc
  linarith

/-- Exact supply for Decomp428c.leaf_minor_sup.
Source: P0082 page 366 after display 27. The real rational bridge and
proved PNTPort Vaughan estimate discharge the prime cancellation input. -/
theorem leaf_minor_sup_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ β ∈ truncatedDomain (F γ N ^ (6 * δ)) (F γ N),
          ‖Sp (F γ N ^ (6 * δ)) (F γ N) β‖ ^ 2 ≤
            C * F γ N ^ (2 - 6 * δ) * Real.log (F γ N) ^ 8 := by
  refine ⟨1 / 30, by norm_num, fun δ hδ hδsmall => ?_⟩
  refine ⟨(14404 : ℝ) ^ 2, by positivity, 8, fun N hN β hβ => ?_⟩
  have hLN : 1 ≤ Real.log (N : ℝ) := by
    have h8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 8) h8
    have hle : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have h2 := Real.log_two_gt_d9
    linarith
  have hpow : 1 ≤ Real.log (N : ℝ) ^ γ := Real.one_le_rpow hLN (by linarith)
  have hX2 : 2 ≤ F γ N := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    exact he.trans (Real.exp_le_exp.mpr hpow)
  have hX1 : 1 ≤ F γ N := by linarith
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hL : 1 ≤ Real.log (F γ N) := by simpa only [F, Real.log_exp] using hpow
  have hP : 1 ≤ F γ N ^ (6 * δ) := Real.one_le_rpow hX1 (by positivity)
  have hPX : F γ N ^ (6 * δ) ≤ F γ N := by
    have hh := Real.rpow_le_rpow_of_exponent_le hX1 (show 6 * δ ≤ 1 by linarith)
    simpa only [Real.rpow_one] using hh
  have hs := PrimeVaughan446.minor_vaughan_real (F γ N ^ (6 * δ)) (F γ N) β hX2 hP hPX hβ.1
  have hc := vaughan_scalar (F γ N) δ hX1 hL hδ.le hδsmall.le
  have hbound := hs.trans hc
  have hp : (F γ N ^ (1 - 3 * δ)) ^ 2 = F γ N ^ (2 - 6 * δ) := by
    rw [← Real.rpow_mul_natCast hX0.le]
    congr 1
    ring
  calc
    _ ≤ (14404 * F γ N ^ (1 - 3 * δ) * Real.log (F γ N) ^ 4) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = (14404 : ℝ) ^ 2 * (F γ N ^ (1 - 3 * δ)) ^ 2 * Real.log (F γ N) ^ 8 := by ring
    _ = _ := by rw [hp]

end LeanLab.ExceptionalSet.UpJ200.MinorSup446
