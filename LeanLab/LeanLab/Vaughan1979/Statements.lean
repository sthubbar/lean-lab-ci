/-
P0090 R. C. Vaughan, A survey of some important problems in additive number theory,
Journées Arithmétiques de Luminy, Astérisque 61 (1979) 213-222,
https://numdam.org/item/AST_1979__61__213_0/, read through a text extraction of the scan.
Its Goldbach sections are a survey; each cited row below is a result AS QUOTED by Vaughan.

* Vaughan [54]: E(x) = O(x exp(−c √(log x))), the strength between the log power saving of
  Chudakov, van der Corput and Estermann and the power saving of Montgomery and Vaughan.
* Schnirelmann's constant: every n > 1 a sum of at most C₀ primes with C₀ = 26, Deshouillers
  [20]; for large n at most 6 primes, Vaughan [56].
PROVED, zero sorry: Montgomery-Vaughan's power saving gives the exp √log saving, which gives the
log power saving, so the chain in ExceptionalSet/Statements.lean gains a middle link; Riesel and
Vaughan's 19 gives 26 gives 27; ternary Goldbach gives the 6 of Vaughan [56].

AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Statements
import LeanLab.SchnirelmannBounds.Statements

namespace LeanLab.Vaughan1979
open Real LeanLab.ExceptionalSet LeanLab.SchnirelmannConstant

/-! ### The exp √log strength -/

/-- `E X ≪ X exp(−c √(log X))` for some `c > 0`. -/
def ExpSqrtLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
    (E X : ℝ) ≤ C * X * Real.exp (-c * Real.sqrt (Real.log X))

/-- CITED, as quoted by Vaughan 1979 from his [54]: `E(x) = O(x exp(−c √(log x)))`. -/
theorem vaughan54 : ExpSqrtLogSaving := by sorry

/-- A power saving gives the exp √log saving, with `c = δ`. -/
theorem expSqrtLog_of_powerSaving (h : PowerSaving) : ExpSqrtLogSaving := by
  obtain ⟨δ, hδ, C, hC⟩ := h
  refine ⟨δ, hδ, max C 0 * Real.exp δ, fun X hX => ?_⟩
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  set L := Real.log X with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hXr
  have hrpow : (X : ℝ) ^ (1 - δ) = X * Real.exp (-δ * L) := by
    calc (X : ℝ) ^ (1 - δ) = Real.exp (L * (1 - δ)) := Real.rpow_def_of_pos hXpos _
      _ = Real.exp L * Real.exp (-δ * L) := by rw [← Real.exp_add]; ring_nf
      _ = X * Real.exp (-δ * L) := by rw [hL, Real.exp_log hXpos]
  have hsq : Real.sqrt L ≤ L + 1 := by
    have h1 := Real.sq_sqrt hL0
    nlinarith [Real.sqrt_nonneg L, sq_nonneg (Real.sqrt L - 1)]
  have hexp : Real.exp (-δ * L) ≤ Real.exp δ * Real.exp (-δ * Real.sqrt L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hM : 0 ≤ max C 0 := le_max_right _ _
  calc (E X : ℝ) ≤ C * (X : ℝ) ^ (1 - δ) := hC X hX
    _ ≤ max C 0 * (X : ℝ) ^ (1 - δ) := by
        gcongr; exact le_max_left _ _
    _ = max C 0 * X * Real.exp (-δ * L) := by rw [hrpow]; ring
    _ ≤ max C 0 * X * (Real.exp δ * Real.exp (-δ * Real.sqrt L)) := by
        gcongr
    _ = max C 0 * Real.exp δ * X * Real.exp (-δ * Real.sqrt L) := by ring

/-- The key inequality: `L^A ≤ (2A/c)^{2A} exp(c √L)` for `L ≥ 0`, `A, c > 0`. -/
theorem rpow_le_exp_sqrt {A c L : ℝ} (hA : 0 < A) (hc : 0 < c) (hL : 0 ≤ L) :
    L ^ A ≤ (2 * A / c) ^ (2 * A) * Real.exp (c * Real.sqrt L) := by
  set w := Real.exp (c * Real.sqrt L) with hw
  have hwpos : 0 < w := Real.exp_pos _
  have hlogw : Real.log w = c * Real.sqrt L := Real.log_exp _
  set ε : ℝ := 1 / (2 * A) with hε
  have hεpos : 0 < ε := by positivity
  -- √L = log w / c ≤ w^ε / (ε c)
  have hsqrt : Real.sqrt L ≤ w ^ ε / (ε * c) := by
    have h1 : Real.log w ≤ w ^ ε / ε := Real.log_le_rpow_div hwpos.le hεpos
    rw [hlogw] at h1
    rw [le_div_iff₀ (by positivity)]
    have h2 := (le_div_iff₀ hεpos).mp h1
    calc Real.sqrt L * (ε * c) = c * Real.sqrt L * ε := by ring
      _ ≤ w ^ ε := h2
  have hLA : L ^ A = Real.sqrt L ^ (2 * A) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL]; ring_nf
  rw [hLA]
  calc Real.sqrt L ^ (2 * A) ≤ (w ^ ε / (ε * c)) ^ (2 * A) :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _) hsqrt (by positivity)
    _ = (w ^ ε) ^ (2 * A) / (ε * c) ^ (2 * A) :=
        Real.div_rpow (by positivity) (by positivity) _
    _ = w / (ε * c) ^ (2 * A) := by
        rw [← Real.rpow_mul hwpos.le, hε]
        have : 1 / (2 * A) * (2 * A) = 1 := by field_simp
        rw [this, Real.rpow_one]
    _ = (2 * A / c) ^ (2 * A) * w := by
        rw [hε]
        have hb : (1 / (2 * A) * c) = (2 * A / c)⁻¹ := by field_simp
        rw [hb, Real.inv_rpow (by positivity), div_inv_eq_mul, mul_comm]

/-- The exp √log saving gives the log power saving. -/
theorem logPowerSaving_of_expSqrtLog (h : ExpSqrtLogSaving) : LogPowerSaving := by
  obtain ⟨c, hc, C, hC⟩ := h
  intro A hA
  refine ⟨max C 0 * (2 * A / c) ^ (2 * A), fun X hX => ?_⟩
  have hX1 : 1 ≤ X := by omega
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlogpos A
  have hkey := rpow_le_exp_sqrt hA hc hlogpos.le
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have hE : (E X : ℝ) ≤ max C 0 * X * Real.exp (-c * Real.sqrt (Real.log X)) :=
    (hC X hX1).trans (by gcongr; exact le_max_left _ _)
  rw [le_div_iff₀ hlogA]
  have hex : Real.exp (-c * Real.sqrt (Real.log X)) * Real.exp (c * Real.sqrt (Real.log X)) = 1 := by
    rw [← Real.exp_add]; simp
  calc (E X : ℝ) * Real.log X ^ A
        ≤ (max C 0 * X * Real.exp (-c * Real.sqrt (Real.log X))) *
          ((2 * A / c) ^ (2 * A) * Real.exp (c * Real.sqrt (Real.log X))) :=
        mul_le_mul hE hkey hlogA.le (by positivity)
    _ = max C 0 * (2 * A / c) ^ (2 * A) * X *
          (Real.exp (-c * Real.sqrt (Real.log X)) * Real.exp (c * Real.sqrt (Real.log X))) := by
        ring
    _ = max C 0 * (2 * A / c) ^ (2 * A) * X := by rw [hex, mul_one]

/-- The chain: Montgomery-Vaughan's power saving gives Vaughan's [54], which gives Estermann's
log power saving. -/
theorem chain (h : PowerSaving) : ExpSqrtLogSaving ∧ LogPowerSaving :=
  ⟨expSqrtLog_of_powerSaving h, logPowerSaving_of_expSqrtLog (expSqrtLog_of_powerSaving h)⟩

/-! ### Schnirelmann's constant as quoted -/

/-- CITED, as quoted by Vaughan 1979 from Deshouillers [20]: every `n > 1` is a sum of at most
26 primes. -/
theorem deshouillers26 : ∀ n : ℕ, 1 < n → AtMostPrimes 26 n := by sorry

/-- CITED, as quoted from Vaughan [56]: every large `n` is a sum of at most 6 primes. -/
theorem vaughan56 : ∃ n0 : ℕ, ∀ n : ℕ, n0 < n → AtMostPrimes 6 n := by sorry

theorem deshouillers26_of_rieselVaughan (h : ∀ n : ℕ, 1 < n → AtMostPrimes 19 n) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 26 n := fun n hn => (h n hn).mono (by norm_num)

theorem vaughan27_of_deshouillers26 (h : ∀ n : ℕ, 1 < n → AtMostPrimes 26 n) :
    ∀ n : ℕ, 1 < n → AtMostPrimes 27 n := fun n hn => (h n hn).mono (by norm_num)

/-- Ternary Goldbach gives Vaughan [56], with `n0 = 1` and 4 in place of 6. -/
theorem vaughan56_of_ternary (hT : TernaryGoldbach) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 < n → AtMostPrimes 6 n :=
  ⟨1, fun n hn => (SchnirelmannBounds.atMost4_of_ternary hT n hn).mono (by norm_num)⟩

end LeanLab.Vaughan1979
