import LeanLab.ExceptionalSet.Decomp450c
import LeanLab.ExceptionalSet.MVVinogradov

/-!
Elementary parameter and finite range helpers from SPLIT_lemma4.
P0082 page 359 omits the analytic discrepancy argument.
These two auxiliary statements use only logarithm growth and the trivial count bound.
They do not supply the omitted discrepancy estimate.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450k

open Real Filter Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- Exact elementary logarithm regime leaf in the formal split of Lemma 4. -/
theorem log_regime_supplied :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        3 ≤ N ∧ 1 ≤ Real.log N ∧ (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) ∧
        (Nat.ceil (Real.log N) : ℝ) ≤ F γ N ^ C := by
  intro γ h1 h2 C hC
  obtain ⟨Nr, hr⟩ := LeanLab.ExceptionalSet.MV.log_rpow_le_rpow_nat
    1 (s := C / 2) (by positivity)
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (C / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < C / 2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Np, hp⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 2)
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nl, hl⟩ := eventually_atTop.mp (hl.eventually_ge_atTop 1)
  refine ⟨max 3 (max Nr (max Np Nl)), fun N hN => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNl : Nl ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hlog : 1 ≤ Real.log (N : ℝ) := hl N hNl
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hceil1 : (1 : ℝ) ≤ (Nat.ceil (Real.log (N : ℝ)) : ℝ) := hlog.trans (Nat.le_ceil _)
  refine ⟨hN3, hlog, hceil1, ?_⟩
  have hceil : (Nat.ceil (Real.log (N : ℝ)) : ℝ) ≤ Real.log (N : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.log (N : ℝ))).le
  have hlogpow := hr N hNr
  rw [Real.rpow_one] at hlogpow
  have hpow := hp N hNp
  have hsquare : ((N : ℝ) ^ (C / 2)) ^ 2 = (N : ℝ) ^ C := by
    rw [← Real.rpow_mul_natCast hNpos.le]
    congr 1
    ring
  have hNF : (N : ℝ) ≤ F γ N := by
    rw [F]
    calc
      _ = Real.exp (Real.log (N : ℝ)) := (Real.exp_log hNpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := Real.rpow_le_rpow_of_exponent_le hlog (by linarith : (1 : ℝ) ≤ γ)
        simpa only [Real.rpow_one] using hh)
  calc
    _ ≤ Real.log (N : ℝ) + 1 := hceil
    _ ≤ ((N : ℝ) ^ (C / 2)) ^ 2 := by nlinarith
    _ = (N : ℝ) ^ C := hsquare
    _ ≤ _ := Real.rpow_le_rpow hNpos.le hNF hC.le

/-- Exact finite range leaf in the formal split of Lemma 4.
The count and its expected term both lie between zero and N. -/
theorem small_N_supplied :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ : ℝ, 0 < κ → ∀ N₀ : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ N₀ → ∀ α z₁ z₂ : ℝ, 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
        |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  classical
  intro γ h1 h2 κ hκ N₀
  let B : ℝ := Real.exp (κ * Real.log (N₀ + 1 : ℕ) ^ (3 - 2 * γ))
  refine ⟨B, (Real.exp_pos _).le, fun N hN hN₀ α z₁ z₂ hz₂ hzz hz₁ => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNnonneg : (0 : ℝ) ≤ N := hNpos.le
  let s := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)
  have hc : (s.card : ℝ) ≤ N := by
    have hc := Finset.card_filter_le (Finset.Ioc (N / 2) N) (fun n : ℕ =>
      z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)
    have hn : s.card ≤ N := hc.trans (by simp only [Nat.card_Ioc]; omega)
    exact_mod_cast hn
  have hc0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hmean0 : 0 ≤ (z₁ - z₂) * N / 2 := by positivity
  have hmean : (z₁ - z₂) * N / 2 ≤ N := by
    have hm := mul_le_mul_of_nonneg_right (by linarith : z₁ - z₂ ≤ 1) hNnonneg
    nlinarith
  have htrivial : |(s.card : ℝ) - (z₁ - z₂) * N / 2| ≤ N := by
    rw [abs_le]
    constructor <;> linarith
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogle : Real.log (N : ℝ) ≤ Real.log (N₀ + 1 : ℕ) :=
    Real.log_le_log hNpos (by exact_mod_cast (by omega : N ≤ N₀ + 1))
  have hrpow := Real.rpow_le_rpow hlog hlogle (by linarith : 0 ≤ 3 - 2 * γ)
  have hscale : 1 ≤ B * Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    dsimp only [B]
    rw [← Real.exp_add, Real.one_le_exp_iff]
    nlinarith [mul_le_mul_of_nonneg_left hrpow hκ.le]
  calc
    _ ≤ (N : ℝ) := htrivial
    _ = (N : ℝ) * 1 := by ring
    _ ≤ (N : ℝ) * (B * Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ))) :=
      mul_le_mul_of_nonneg_left hscale hNnonneg
    _ = _ := by ring

end LeanLab.ExceptionalSet.Decomp450k
