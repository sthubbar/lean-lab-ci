/-
The log power version of `powerBound_of_window`, unit U-1018, run 20261019T0202Z-9877, T2,
P0015 skeleton, the next action of MVSKELETON.md: a dyadic window bound
`#{bad even n in (x/2, x]} ≤ C x / (log x)^A` for `x ≥ X0` gives `E X ≤ K X / (log X)^A` for every
`X ≥ 2`. With `minorTerm_le_sup` and Vinogradov's minor arc bound this is the Estermann 1938
strength, `LogPowerSaving`, once the major arc input is supplied.
Proof: strong induction, `E x ≤ E ⌊x/2⌋ + badWindow x`, with `(log x)^A ≤ (4/3) (log (x/3))^A`
for `log x ≥ r log 3 / (r - 1)`, `r = (4/3)^{1/A}`, so the half step costs a factor `2/3`.
KNOWN mathematics. AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.MVConditional

open Real

namespace LeanLab.ExceptionalSet.MV

/-- `(log x)^A ≤ (4/3) (log (x/3))^A` once `log x ≥ r log 3 / (r - 1)`, `r = (4/3)^{1/A}`. -/
lemma log_pow_le_of_large {A x : ℝ} (hA : 0 < A) (hx3 : 3 < x)
    (hL : log 3 * (4 / 3 : ℝ) ^ (1 / A) / ((4 / 3 : ℝ) ^ (1 / A) - 1) ≤ log x) :
    log x ^ A ≤ 4 / 3 * log (x / 3) ^ A := by
  set r := (4 / 3 : ℝ) ^ (1 / A) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  have hl3 : 0 < log 3 := log_pos (by norm_num)
  have hx0 : 0 < x := by linarith
  have hlx3 : log (x / 3) = log x - log 3 := log_div hx0.ne' (by norm_num)
  have hpos3 : 0 < log (x / 3) := log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have hlx0 : 0 < log x := log_pos (by linarith)
  have key : log x ≤ r * log (x / 3) := by
    rw [hlx3]
    have h1 : log 3 * r ≤ log x * (r - 1) := by
      rw [div_le_iff₀ (by linarith)] at hL; linarith
    nlinarith
  have hrA : r ^ A = 4 / 3 := by
    rw [hr, ← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hA.ne', Real.rpow_one]
  calc log x ^ A ≤ (r * log (x / 3)) ^ A := Real.rpow_le_rpow hlx0.le key hA.le
    _ = r ^ A * log (x / 3) ^ A := Real.mul_rpow (by linarith) hpos3.le
    _ = 4 / 3 * log (x / 3) ^ A := by rw [hrA]

/-- **Log power dyadic summation.** A window bound `badWindow x ≤ C x / (log x)^A` for `x ≥ X0`
gives `E X ≤ K X / (log X)^A` for every `X ≥ 2`. An implication lemma, PROVED. -/
theorem logPower_of_window {A C : ℝ} {X0 : ℕ} (hA : 0 < A)
    (h : ∀ x : ℕ, X0 ≤ x → (badWindow x : ℝ) ≤ C * x / log x ^ A) :
    ∃ K : ℝ, ∀ X : ℕ, 2 ≤ X → (E X : ℝ) ≤ K * X / log X ^ A := by
  set r := (4 / 3 : ℝ) ^ (1 / A) with hr
  set L1 := log 3 * r / (r - 1) with hL1
  set X1 : ℕ := max X0 (max 6 ⌈exp L1⌉₊) with hX1
  set K : ℝ := max (3 * |C|) (log X1 ^ A) with hK
  refine ⟨K, ?_⟩
  have hK0 : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
  intro X
  induction X using Nat.strong_induction_on with
  | _ x ih =>
    intro hx2
    have hx2r : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    have hlx : 0 < log x := log_pos (by linarith)
    have hlxA : 0 < log x ^ A := Real.rpow_pos_of_pos hlx A
    by_cases hsmall : x < X1
    · -- base: E x ≤ x ≤ K x / (log x)^A since (log x)^A ≤ (log X1)^A ≤ K
      have hX1r : (x : ℝ) ≤ X1 := by exact_mod_cast hsmall.le
      have hpow : log x ^ A ≤ log X1 ^ A :=
        Real.rpow_le_rpow hlx.le (log_le_log (by linarith) hX1r) hA.le
      have hKA : log x ^ A ≤ K := hpow.trans (le_max_right _ _)
      calc (E x : ℝ) ≤ x := by exact_mod_cast E_le x
        _ = log x ^ A * x / log x ^ A := by field_simp
        _ ≤ K * x / log x ^ A := by gcongr
    · push_neg at hsmall
      have hx6 : 6 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hsmall
      have hX0 : X0 ≤ x := le_trans (le_max_left _ _) hsmall
      have hxe : exp L1 ≤ x := by
        have : ⌈exp L1⌉₊ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hsmall
        exact (Nat.le_ceil _).trans (by exact_mod_cast this)
      have hx6r : (6 : ℝ) ≤ x := by exact_mod_cast hx6
      have hLx : L1 ≤ log x := by
        rw [← log_exp L1]; exact log_le_log (exp_pos _) hxe
      have hkey := log_pow_le_of_large hA (by linarith) hLx
      -- the half step
      have hsplit : (E x : ℝ) ≤ E (x / 2) + badWindow x := by exact_mod_cast E_le_split (x / 2) x
      have hh2 : 2 ≤ x / 2 := by omega
      have hih := ih (x / 2) (by omega) hh2
      have hhr : ((x / 2 : ℕ) : ℝ) ≤ (x : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self x 2
      have hh3 : (x : ℝ) / 3 ≤ ((x / 2 : ℕ) : ℝ) := by
        have : x ≤ 3 * (x / 2) := by omega
        rw [div_le_iff₀ (by norm_num)]; have := (Nat.cast_le (α := ℝ)).2 this; push_cast at this
        linarith
      have hl3pos : 0 < log ((x : ℝ) / 3) := log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
      have hl3A : 0 < log ((x : ℝ) / 3) ^ A := Real.rpow_pos_of_pos hl3pos A
      have hlog_half : log ((x : ℝ) / 3) ^ A ≤ log ((x / 2 : ℕ) : ℝ) ^ A :=
        Real.rpow_le_rpow hl3pos.le (log_le_log (by linarith) hh3) hA.le
      have hE2 : (E (x / 2) : ℝ) ≤ K * ((x : ℝ) / 2) / log ((x : ℝ) / 3) ^ A := by
        refine hih.trans ?_
        rw [div_le_div_iff₀ (Real.rpow_pos_of_pos (lt_of_lt_of_le hl3pos (log_le_log (by linarith) hh3)) A) hl3A]
        have h1 : K * ((x / 2 : ℕ) : ℝ) ≤ K * ((x : ℝ) / 2) := mul_le_mul_of_nonneg_left hhr hK0
        have h2 : 0 ≤ K * ((x : ℝ) / 2) := by positivity
        calc K * ((x / 2 : ℕ) : ℝ) * log ((x : ℝ) / 3) ^ A
            ≤ K * ((x : ℝ) / 2) * log ((x : ℝ) / 3) ^ A := by gcongr
          _ ≤ K * ((x : ℝ) / 2) * log ((x / 2 : ℕ) : ℝ) ^ A := by gcongr
      have hE2' : K * ((x : ℝ) / 2) / log ((x : ℝ) / 3) ^ A ≤ 2 / 3 * (K * x / log x ^ A) := by
        rw [div_le_iff₀ hl3A]
        have : 2 / 3 * (K * x / log x ^ A) * log ((x : ℝ) / 3) ^ A
            = K * x / 2 * (4 / 3 * log ((x : ℝ) / 3) ^ A) / log x ^ A := by ring
        rw [this, le_div_iff₀ hlxA]
        have hKx : 0 ≤ K * x / 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hkey hKx]
      have hW := h x hX0
      have hC : C ≤ K / 3 := by
        have := le_max_left (3 * |C|) (log X1 ^ A); rw [← hK] at this
        linarith [le_abs_self C]
      have hW' : C * x / log x ^ A ≤ K / 3 * x / log x ^ A := by gcongr
      calc (E x : ℝ) ≤ E (x / 2) + badWindow x := hsplit
        _ ≤ 2 / 3 * (K * x / log x ^ A) + K / 3 * x / log x ^ A := by linarith
        _ = K * x / log x ^ A := by ring

/-- Window bounds at every log power give `LogPowerSaving`, the Estermann form. -/
theorem logPowerSaving_of_windows
    (h : ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X0 : ℕ), ∀ x : ℕ, X0 ≤ x →
      (badWindow x : ℝ) ≤ C * x / log x ^ A) : LogPowerSaving := by
  intro A hA
  obtain ⟨C, X0, hC⟩ := h A hA
  exact logPower_of_window hA hC

#print axioms log_pow_le_of_large
#print axioms logPower_of_window
#print axioms logPowerSaving_of_windows

end LeanLab.ExceptionalSet.MV
