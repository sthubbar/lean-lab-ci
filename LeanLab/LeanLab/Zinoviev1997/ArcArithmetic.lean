/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Elementary error bookkeeping in Lemmas 3.1 and 3.2, pages 349 to 356.
The pointwise approximation is a cited GRH input.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ArcInputs

namespace LeanLab.Zinoviev1997
open Real Finset ArithmeticFunction LeanLab.CircleOrth MeasureTheory
open scoped ArithmeticFunction.Moebius

/-- The cubic perturbation estimate behind display 3.6. -/
theorem cube_difference_bound (s m : ℂ) (ε : ℝ) (h : ‖s - m‖ ≤ ε) :
    ‖s ^ 3 - m ^ 3‖ ≤ 3 * ‖m‖ ^ 2 * ε + 3 * ‖m‖ * ε ^ 2 + ε ^ 3 := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans h
  have he : s ^ 3 - m ^ 3 =
      3 * m ^ 2 * (s - m) + 3 * m * (s - m) ^ 2 + (s - m) ^ 3 := by ring
  rw [he]
  calc
    _ ≤ ‖3 * m ^ 2 * (s - m) + 3 * m * (s - m) ^ 2‖ + ‖(s - m) ^ 3‖ :=
      norm_add_le _ _
    _ ≤ (‖3 * m ^ 2 * (s - m)‖ + ‖3 * m * (s - m) ^ 2‖) + ‖(s - m) ^ 3‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = 3 * ‖m‖ ^ 2 * ‖s - m‖ + 3 * ‖m‖ * ‖s - m‖ ^ 2 + ‖s - m‖ ^ 3 := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
    _ ≤ _ := by gcongr

/-- The constants 12, 48 and 64 in display 3.6 come from cubing a 4B error. -/
theorem cube_scaled_error (s M c : ℂ) (φ B : ℝ) (hφ : 0 < φ) (hB : 0 ≤ B)
    (hc : ‖c‖ ≤ 1 / φ) (hs : ‖s - c * M‖ ≤ 4 * B) :
    ‖s ^ 3 - (c * M) ^ 3‖ ≤
      12 * ‖M‖ ^ 2 / φ ^ 2 * B + 48 * ‖M‖ / φ * B ^ 2 + 64 * B ^ 3 := by
  have hm : ‖c * M‖ ≤ ‖M‖ / φ := by
    rw [norm_mul]
    calc ‖c‖ * ‖M‖ ≤ (1 / φ) * ‖M‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = ‖M‖ / φ := by ring
  calc
    _ ≤ 3 * ‖c * M‖ ^ 2 * (4 * B) + 3 * ‖c * M‖ * (4 * B) ^ 2 + (4 * B) ^ 3 :=
      cube_difference_bound s (c * M) (4 * B) hs
    _ ≤ 3 * (‖M‖ / φ) ^ 2 * (4 * B) + 3 * (‖M‖ / φ) * (4 * B) ^ 2 + (4 * B) ^ 3 := by
      gcongr
    _ = _ := by ring

/-- The nonconstant part of the error in Lemma 3.1. -/
noncomputable def lemma31Base (N q : ℕ) : ℝ :=
  (Nat.totient q + 4 * Real.pi * Real.log N) * Real.sqrt N * Real.log N ^ 2

/-- Lemma 3.1 on page 349, in the paper's Fourier signs.
This remains a cited GRH input. -/
def Lemma31Input (N : ℕ) : Prop :=
  ∀ q ∈ Finset.Icc 1 (arcCutoff N), ∀ a ∈ Finset.range q, Nat.Coprime a q →
    ∀ z : ℝ, |z| ≤ arcRadius N q →
      ‖SZ N (-((a : ℝ) / q + z)) -
        (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * modelSum N (-z)‖ ≤
          4 * lemma31Base N q

theorem lemma31Base_nonneg (N q : ℕ) : 0 ≤ lemma31Base N q := by
  unfold lemma31Base
  have := Real.log_natCast_nonneg N
  positivity

theorem norm_moebius_ratio (q : ℕ) (hq : 0 < q) :
    ‖(((μ q : ℝ) / Nat.totient q : ℝ) : ℂ)‖ ≤ 1 / (Nat.totient q : ℝ) := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hφ]
  apply div_le_div_of_nonneg_right _ hφ.le
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))

/-- Display 3.6, CONDITIONAL ON Lemma31Input only. -/
theorem lemma31_cubic (N : ℕ) (h : Lemma31Input N)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (a : ℕ) (ha : a ∈ Finset.range q) (hac : Nat.Coprime a q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖SZ N (-((a : ℝ) / q + z)) ^ 3 -
        ((((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * modelSum N (-z)) ^ 3‖ ≤
      12 * ‖modelSum N (-z)‖ ^ 2 / (Nat.totient q : ℝ) ^ 2 * lemma31Base N q +
      48 * ‖modelSum N (-z)‖ / Nat.totient q * lemma31Base N q ^ 2 +
      64 * lemma31Base N q ^ 3 := by
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  apply cube_scaled_error _ _ _ _ _
    (by exact_mod_cast Nat.totient_pos.mpr hq0) (lemma31Base_nonneg N q)
    (norm_moebius_ratio q hq0)
  exact h q hq a ha hac z hz

/-- The five error budgets on pages 353 to 356 leave room below 0.04 N squared. -/
theorem lemma32_error_budget (N : ℝ) (r₁ r₂ r₃ r₄ r₅ : ℂ)
    (h₁ : ‖r₁‖ ≤ 0.0008 * N ^ 2) (h₂ : ‖r₂‖ ≤ 0.012 * N ^ 2)
    (h₃ : ‖r₃‖ ≤ 0.003 * N ^ 2) (h₄ : ‖r₄‖ ≤ 0.003 * N ^ 2)
    (h₅ : ‖r₅‖ ≤ 0.015 * N ^ 2) :
    ‖r₁ + r₂ + r₃ + r₄ + r₅‖ ≤ 0.0338 * N ^ 2 := by
  have ha := norm_add_le (r₁ + r₂ + r₃ + r₄) r₅
  have hb := norm_add_le (r₁ + r₂ + r₃) r₄
  have hc := norm_add_le (r₁ + r₂) r₃
  have hd := norm_add_le r₁ r₂
  linarith

/-- Lemma32Input follows from an exact remainder split and the five cited error bounds.
This is CONDITIONAL ON the remainder split and those bounds. -/
theorem lemma32_of_error_terms (N : ℕ) (σ : ℝ) (r₁ r₂ r₃ r₄ r₅ : ℂ)
    (he : (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs N,
      SZ N α ^ 3 * ee (-((N : ℤ) * α))) - (σ : ℂ) * modelIntegral N =
        r₁ + r₂ + r₃ + r₄ + r₅)
    (h₁ : ‖r₁‖ ≤ 0.0008 * (N : ℝ) ^ 2) (h₂ : ‖r₂‖ ≤ 0.012 * (N : ℝ) ^ 2)
    (h₃ : ‖r₃‖ ≤ 0.003 * (N : ℝ) ^ 2) (h₄ : ‖r₄‖ ≤ 0.003 * (N : ℝ) ^ 2)
    (h₅ : ‖r₅‖ ≤ 0.015 * (N : ℝ) ^ 2) : Lemma32Input N σ := by
  unfold Lemma32Input
  rw [he]
  have h := lemma32_error_budget N r₁ r₂ r₃ r₄ r₅ h₁ h₂ h₃ h₄ h₅
  nlinarith [sq_nonneg (N : ℝ)]

end LeanLab.Zinoviev1997
