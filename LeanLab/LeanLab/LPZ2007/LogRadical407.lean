import LeanLab.LPZ2007.Iwaniec106

/-!
P0045 preprint page 6, the paragraph after Corollary 4.2.
The quoted Iwaniec region implies log of the odd radical is at least c log X.
This strengthens the quadratic consequence already proved in Iwaniec106.
The analytic region remains an explicit hypothesis.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.LogRadical407

open Real Filter Asymptotics Eq14FromCor42

/-- P0045 page 6, the sublinear term in the quoted Iwaniec denominator.
The odd radical term is kept separate rather than bounded by log squared X. -/
theorem denominator_majorant {X P T : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hXpos : 0 < X) (hX : 1 ≤ log X) (hT : 1 ≤ T) (hTX : log (T + 2) ≤ log X)
    (hXP : P ≤ X ^ (0.41 : ℝ)) (hrP : (r : ℝ) ≤ P)
    {t : ℝ} (ht : |t| ≤ T) :
    iwB r t ≤ 40000 * log (2 * (oddRad r : ℝ)) +
      40000 * (log (2 * (4 * log X) ^ 2) +
        ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hargpos : 0 < (r : ℝ) * (|t| + 2) := by positivity
  have hargle : (r : ℝ) * (|t| + 2) ≤ X ^ (0.41 : ℝ) * (T + 2) :=
    mul_le_mul (hrP.trans hXP) (by linarith) (by positivity) (by positivity)
  have hell : log ((r : ℝ) * (|t| + 2)) ≤ 2 * log X := by
    have hh := log_le_log hargpos hargle
    rw [log_mul (by positivity : (X ^ (0.41 : ℝ)) ≠ 0)
      (by linarith : T + 2 ≠ 0), log_rpow hXpos] at hh
    linarith
  have hellLower : log 2 ≤ log ((r : ℝ) * (|t| + 2)) :=
    log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  have hell0 : 0 < log ((r : ℝ) * (|t| + 2)) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hellLower
  have hlogell : log (2 * log ((r : ℝ) * (|t| + 2))) ≤ log (4 * log X) :=
    log_le_log (by positivity) (by linarith)
  have hlogu0 : 0 ≤ log (4 * log X) := log_nonneg (by linarith)
  have hprod : log ((r : ℝ) * (|t| + 2)) *
      log (2 * log ((r : ℝ) * (|t| + 2))) ≤ (4 * log X) * log (4 * log X) := by
    calc
      _ ≤ log ((r : ℝ) * (|t| + 2)) * log (4 * log X) :=
        mul_le_mul_of_nonneg_left hlogell hell0.le
      _ ≤ (4 * log X) * log (4 * log X) :=
        mul_le_mul_of_nonneg_right (by linarith) hlogu0
  have hprod0 : 0 ≤ log ((r : ℝ) * (|t| + 2)) *
      log (2 * log ((r : ℝ) * (|t| + 2))) := by
    exact mul_nonneg hell0.le (log_nonneg (by linarith [log_two_gt_d9]))
  have hp := rpow_le_rpow hprod0 hprod (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hlogextra : 0 ≤ log (2 * (4 * log X) ^ 2) := log_nonneg (by nlinarith)
  unfold iwB
  dsimp
  nlinarith

/-- P0045 page 6, the stronger conclusion stated after the Iwaniec region.
For each fixed H and T, nonreal exceptional moduli have exponentially large odd radical.
This is CONDITIONAL ON the quoted IwaniecZeroFree region only. -/
theorem nonreal_log_radical_growth (hiw : IwaniecZeroFree)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X P : ℝ, X0 ≤ X → PRange X P →
      ∀ z ∈ EZero X H T P, (∃ a, (z.2.1 a).im ≠ 0) →
        c * Lg X ≤ log (oddRad z.1 : ℝ) := by
  have hHpos : 0 < H := by linarith
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1
    (Iwaniec106.logarithmic_error_isLittleO.bound
      (by positivity : (0 : ℝ) < 1 / (8 * H)))
  let V := max 1 (max (log (T + 2)) (max (U / 4) (160000 * H * log 2)))
  refine ⟨log 2 / (160000 * H), exp V, by positivity, ?_⟩
  intro X P hX hP z hz hreal
  have hXpos : 0 < X := (exp_pos V).trans_le hX
  have hVX : V ≤ log X := by
    have hh := log_le_log (exp_pos V) hX
    simpa only [log_exp] using hh
  have hlog : 1 ≤ log X := (le_max_left _ _).trans hVX
  have hTX : log (T + 2) ≤ log X :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hVX)
  have hUX : U ≤ 4 * log X := by
    have hh : U / 4 ≤ log X := (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hVX))
    linarith
  have hlarge : 160000 * H * log 2 ≤ log X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hVX))
  have hXone : 1 < X := by
    by_contra hh
    have hh' : log X ≤ 0 := log_nonpos hXpos.le (by linarith)
    linarith
  have hconstraint := Iwaniec106.nonreal_zero_constraint hiw hXone z hz hreal
  have hB := denominator_majorant hz.1 hXpos hlog hT hTX hP.2 hz.2.1 hz.2.2.2.2.2
  have hsmall := hU (4 * log X) hUX
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 4 * log X)] at hsmall
  have herror : 40000 * (log (2 * (4 * log X) ^ 2) +
      ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ)) ≤ log X / (2 * H) := by
    calc
      _ ≤ |40000 * (log (2 * (4 * log X) ^ 2) +
          ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ))| := le_abs_self _
      _ ≤ 1 / (8 * H) * (4 * log X) := hsmall
      _ = log X / (2 * H) := by field_simp <;> ring
  have hradpos : (0 : ℝ) < oddRad z.1 := by exact_mod_cast oddRad_pos z.1
  have hradlog : log (2 * (oddRad z.1 : ℝ)) = log 2 + log (oddRad z.1 : ℝ) :=
    log_mul (by norm_num) hradpos.ne'
  have hmain := mul_le_mul_of_nonneg_left (hB.trans
    (add_le_add (le_refl (40000 * log (2 * (oddRad z.1 : ℝ)))) herror)) hHpos.le
  rw [hradlog] at hmain
  have he : H * (log X / (2 * H)) = log X / 2 := by field_simp <;> ring
  have hlog2pos : 0 < log 2 := Real.log_pos (by norm_num)
  have hident : log 2 / (160000 * H) * Lg X = log X / (160000 * H) := by
    unfold Lg Real.logb
    field_simp
  rw [hident, div_le_iff₀ (by positivity : 0 < 160000 * H)]
  nlinarith [he]

end LeanLab.LPZ2007.LogRadical407

#print axioms LeanLab.LPZ2007.LogRadical407.denominator_majorant
#print axioms LeanLab.LPZ2007.LogRadical407.nonreal_log_radical_growth
