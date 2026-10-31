import LeanLab.Ternary78.BennettGrowth

/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 2005.02989 v1 printed page 3 Conjecture 1.3 and the paragraph below it.
The printed conjecture is kept as a Prop. A sufficient height variant has a separate name.
-/

namespace LeanLab.Ternary78.Bennett
open Real

/-- Conjecture 1.3 at one fixed height, for primitive characters of conductor q. -/
def CountGrowthAt (N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ) (T : ℝ) : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∃ q₀ : ℕ, 2 ≤ q₀ ∧
    ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → M ≤ N q χ T

/-- Printed Conjecture 1.3. This is not a proved theorem. -/
def BennettConj1_3 (N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ) : Prop :=
  ∀ T : ℝ, 0 < T → CountGrowthAt N T

/-- The growth range claimed in the paragraph after Conjecture 1.3.
This records the printed range unchanged and is not asserted as proved. -/
def PrintedGrowthRange (N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ) : Prop :=
  ∀ T : ℝ, 5 / 7 + 1e-5 ≤ T → CountGrowthAt N T

/-- The printed endpoint does not give a positive leading coefficient
in the displayed Theorem 1.1 lower bound. This is a real arithmetic fact only. -/
theorem printed_growth_slope_negative :
    (5 / 7 + 1e-5 : ℝ) / Real.pi < 0.22737 := by
  apply (div_lt_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_d6]

/-- A separate conservative decimal height has a positive coefficient. -/
theorem growth_slope_positive :
    (0.22737 : ℝ) < (0.71431 : ℝ) / Real.pi := by
  apply (lt_div_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_lt_d6]

/-- A consistency instance for the conjecture as an abstract count statement. -/
example : BennettConj1_3 (fun q _ _ => q) := by
  intro T hT M hM
  refine ⟨max 2 M, le_max_left _ _, ?_⟩
  intro q _ hq χ hχ
  exact (le_max_right 2 M).trans hq

#print axioms printed_growth_slope_negative
#print axioms growth_slope_positive

/-- A logarithmic tangent turns the exact lower endpoint into an affine function of log q. -/
theorem lowerEndpoint_affine {T a : ℝ} (hT : 0 < T) (ha : 0 < a) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      1.567 < log (q * (T + 2) / (2 * Real.pi)) →
      (T / Real.pi - 0.22737 - 2 / a) * log q + C ≤ lowerEndpoint χ T := by
  let b : ℝ := log ((T + 2) / (2 * Real.pi))
  let d : ℝ := log (T / (2 * Real.pi * exp 1))
  refine ⟨T / Real.pi * d + 1 / 4 - 0.22737 * b - 2 * log a - 2 * (1 + b) / a + 2, ?_⟩
  intro q _ χ hl
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hm : log (q * T / (2 * Real.pi * exp 1)) = log q + d := by
    rw [show (q : ℝ) * T / (2 * Real.pi * exp 1) = q * (T / (2 * Real.pi * exp 1)) by ring,
      log_mul (ne_of_gt hq) (by positivity)]
  have he : log (q * (T + 2) / (2 * Real.pi)) = log q + b := by
    rw [show (q : ℝ) * (T + 2) / (2 * Real.pi) = q * ((T + 2) / (2 * Real.pi)) by ring,
      log_mul (ne_of_gt hq) (by positivity)]
  have hp : 0 < 1 + (log q + b) := by rw [he] at hl; linarith
  have htangent := log_le_sub_one_of_pos (div_pos hp ha)
  rw [log_div (ne_of_gt hp) (ne_of_gt ha)] at htangent
  have hpar : (χ (-1) : ℂ).re ≤ 1 :=
    (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (χ.norm_le_one _))
  unfold lowerEndpoint
  rw [hm, he]
  ring_nf at htangent ⊢
  linarith

#print axioms lowerEndpoint_affine

/-- CONDITIONAL ON BennettThm1_1 at every modulus bound. This proves conductor
growth when the printed lower bound has a positive leading coefficient. -/
theorem countGrowthAt_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ}
    (hB : ∀ Q, BennettThm1_1 N Q) {T : ℝ} (hT : 5 / 7 ≤ T)
    (hslope : 0.22737 < T / Real.pi) : CountGrowthAt N T := by
  have hT0 : 0 < T := by linarith
  let δ : ℝ := T / Real.pi - 0.22737
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let a : ℝ := 4 / δ
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨C, hC⟩ := lowerEndpoint_affine hT0 ha
  have hcoef : T / Real.pi - 0.22737 - 2 / a = δ / 2 := by
    change δ - 2 / (4 / δ) = δ / 2
    field_simp
    ring
  let b : ℝ := log ((T + 2) / (2 * Real.pi))
  intro M _hM
  let L : ℝ := max (((M : ℝ) - C) / (δ / 2)) (2 + |b|)
  refine ⟨max 2 ⌈exp L⌉₊, le_max_left _ _, ?_⟩
  intro q _ hq χ hχ
  have hq2 : 2 ≤ q := (le_max_left 2 ⌈exp L⌉₊).trans hq
  have hq1 : 1 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqceil : ⌈exp L⌉₊ ≤ q := (le_max_right 2 ⌈exp L⌉₊).trans hq
  have hqexp : exp L ≤ (q : ℝ) := (Nat.le_ceil (exp L)).trans (by exact_mod_cast hqceil)
  have hlog : L ≤ log (q : ℝ) := (Real.le_log_iff_exp_le hqr).mpr hqexp
  have hl : 1.567 < log (q * (T + 2) / (2 * Real.pi)) := by
    have hLb : 2 + |b| ≤ log (q : ℝ) := (le_max_right _ _).trans hlog
    have he : log (q * (T + 2) / (2 * Real.pi)) = log q + b := by
      rw [show (q : ℝ) * (T + 2) / (2 * Real.pi) = q * ((T + 2) / (2 * Real.pi)) by ring,
        log_mul (ne_of_gt hqr) (by positivity)]
    rw [he]
    linarith [neg_abs_le b]
  have htarget : (M : ℝ) ≤ δ / 2 * log q + C := by
    have hLtarget : ((M : ℝ) - C) / (δ / 2) ≤ log q := (le_max_left _ _).trans hlog
    have h := (div_le_iff₀ (half_pos hδ)).mp hLtarget
    nlinarith
  have he := hC q χ hl
  rw [hcoef] at he
  have hcount := lowerEndpoint_le_count (hB q) le_rfl hq1 χ hχ hT hl
  have hfinal : (M : ℝ) ≤ (N q χ T : ℝ) :=
    htarget.trans (he.trans ((le_max_right _ _).trans hcount))
  exact_mod_cast hfinal

#print axioms countGrowthAt_of_bennett

/-- CONDITIONAL ON BennettThm1_1 at every modulus bound.
This separate conservative height range does not alter PrintedGrowthRange. -/
theorem countGrowthAt_above_071431
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ}
    (hB : ∀ Q, BennettThm1_1 N Q) {T : ℝ} (hT : 0.71431 ≤ T) : CountGrowthAt N T := by
  apply countGrowthAt_of_bennett hB
  · linarith
  · exact growth_slope_positive.trans_le (div_le_div_of_nonneg_right hT Real.pi_pos.le)

/-- Printed Conjecture 1.4. This is not a proved theorem or a cited input used above. -/
def BennettConj1_4 (N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ) : Prop :=
  ∀ (q : ℕ) [NeZero q], 1 < q → ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ T : ℝ, 5 / 7 ≤ T →
      let l := log (q * (T + 2) / (2 * Real.pi));
      |(N q χ T : ℝ) - (T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) -
        (χ (-1) : ℂ).re / 4)| ≤ l / log (2 + l)

#print axioms countGrowthAt_above_071431

end LeanLab.Ternary78.Bennett
