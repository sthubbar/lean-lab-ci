import LeanLab.LPZ2007.Eq14FromCor42

/-!
Elementary consequences of the Iwaniec region quoted on P0045 page 6.
The region itself remains a cited input.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Iwaniec106

open Real Filter Asymptotics Eq14FromCor42

/-- The denominator in the quoted zero free region is positive. -/
theorem iwB_pos {r : ℕ} (hr : 1 ≤ r) (t : ℝ) : 0 < iwB r t := by
  have hrad : (1 : ℝ) ≤ oddRad r := by exact_mod_cast oddRad_pos r
  have hlograd : 0 < log (2 * (oddRad r : ℝ)) := log_pos (by linarith)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have harg : (2 : ℝ) ≤ r * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hell : log 2 ≤ log ((r : ℝ) * (|t| + 2)) :=
    log_le_log (by norm_num) harg
  have hell0 : 0 ≤ log ((r : ℝ) * (|t| + 2)) :=
    log_nonneg (by linarith)
  have hlogell : 0 ≤ log (2 * log ((r : ℝ) * (|t| + 2))) :=
    log_nonneg (by linarith [log_two_gt_d9])
  have hp := rpow_nonneg (mul_nonneg hell0 hlogell) (3 / 4 : ℝ)
  unfold iwB
  dsimp
  positivity

/-- The quoted region forces log X at most H times its denominator
for a nonreal character zero in the exceptional box. P0045 page 6. -/
theorem nonreal_zero_constraint (hiw : IwaniecZeroFree)
    {X H T P : ℝ} (hX : 1 < X)
    (z : Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (hz : z ∈ EZero X H T P) (hreal : ∃ a, (z.2.1 a).im ≠ 0) :
    log X ≤ H * iwB z.1 z.2.2.im := by
  have hB := iwB_pos hz.1 z.2.2.im
  have hlog := log_pos hX
  have hupper : z.2.2.re ≤ 1 - 1 / iwB z.1 z.2.2.im := by
    by_contra h
    have hlt : 1 - 1 / iwB z.1 z.2.2.im < z.2.2.re := by linarith
    exact hiw z.1 hz.1 z.2.1 hz.2.2.1 hreal z.2.2 hlt hz.2.2.2.1
  have hnear := hz.2.2.2.2.1
  have hdiv : 1 / iwB z.1 z.2.2.im ≤ H / log X := by linarith
  have hh := (div_le_div_iff₀ hB hlog).mp hdiv
  simpa only [one_mul] using hh

/-- The elementary logarithmic error in the quoted region is sublinear.
This is the asymptotic calculation used on P0045 page 6. -/
theorem logarithmic_error_isLittleO :
    (fun u : ℝ => 40000 * (log (2 * u ^ 2) + (u * log u) ^ (3 / 4 : ℝ)))
      =o[Filter.atTop] (fun u : ℝ => u) := by
  have hlog : (fun u : ℝ => log (2 * u ^ 2)) =o[atTop] (fun u : ℝ => u) := by
    have h := (isLittleO_const_id_atTop (log 2)).add
      (Real.isLittleO_log_id_atTop.const_mul_left 2)
    apply h.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [log_mul (by norm_num) (by positivity), log_pow]
    norm_num
  have hprod : (fun u : ℝ => u * log u) =o[Filter.atTop]
      (fun u : ℝ => u ^ (4 / 3 : ℝ)) := by
    have h := (Asymptotics.isBigO_refl (fun u : ℝ => u) Filter.atTop).mul_isLittleO
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
    apply h.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
    calc
      u * u ^ (1 / 3 : ℝ) = u ^ (1 : ℝ) * u ^ (1 / 3 : ℝ) := by rw [rpow_one]
      _ = u ^ (4 / 3 : ℝ) := by rw [← rpow_add hu]; norm_num
  have hpow : (fun u : ℝ => (u * log u) ^ (3 / 4 : ℝ)) =o[Filter.atTop]
      (fun u : ℝ => u) := by
    have h := hprod.rpow (by norm_num : (0 : ℝ) < 3 / 4)
      ((Filter.eventually_ge_atTop (0 : ℝ)).mono fun u hu => rpow_nonneg hu (4 / 3 : ℝ))
    apply h.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
    rw [← rpow_mul hu]
    norm_num
  exact (hlog.add hpow).const_mul_left 40000

/-- A small odd radical gives a uniform sublinear upper majorant for iwB.
This is the elementary comparison behind P0045 page 6. -/
theorem iwB_le_logarithmic_error {X P T : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hXpos : 0 < X) (hX : 1 ≤ log X) (hT : 1 ≤ T) (hTX : log (T + 2) ≤ log X)
    (hXP : P ≤ X ^ (0.41 : ℝ)) (hrP : (r : ℝ) ≤ P)
    {t : ℝ} (ht : |t| ≤ T) (hrad : (oddRad r : ℝ) ≤ (log X) ^ 2) :
    iwB r t ≤ 40000 * (log (2 * (4 * log X) ^ 2) +
      ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hradpos : (0 : ℝ) < oddRad r := by exact_mod_cast oddRad_pos r
  have hargpos : 0 < (r : ℝ) * (|t| + 2) := by positivity
  have hargle : (r : ℝ) * (|t| + 2) ≤ X ^ (0.41 : ℝ) * (T + 2) :=
    mul_le_mul (hrP.trans hXP) (by linarith) (by positivity) (by positivity)
  have hell : log ((r : ℝ) * (|t| + 2)) ≤ 2 * log X := by
    have hh := log_le_log hargpos hargle
    rw [log_mul (by positivity : (X ^ (0.41 : ℝ)) ≠ 0) (by linarith : T + 2 ≠ 0), log_rpow hXpos] at hh
    linarith
  have hell0 : 0 ≤ log ((r : ℝ) * (|t| + 2)) :=
    log_nonneg (by nlinarith [abs_nonneg t])
  have hlogell : log (2 * log ((r : ℝ) * (|t| + 2))) ≤ log (4 * log X) := by
    by_cases he : log ((r : ℝ) * (|t| + 2)) = 0
    · simp only [he, mul_zero, log_zero]
      exact log_nonneg (by linarith)
    · exact log_le_log (by positivity) (by linarith)
  have hlogu0 : 0 ≤ log (4 * log X) := log_nonneg (by linarith)
  have hprod : log ((r : ℝ) * (|t| + 2)) *
      log (2 * log ((r : ℝ) * (|t| + 2))) ≤ (4 * log X) * log (4 * log X) := by
    calc
      _ ≤ log ((r : ℝ) * (|t| + 2)) * log (4 * log X) :=
        mul_le_mul_of_nonneg_left hlogell hell0
      _ ≤ (4 * log X) * log (4 * log X) :=
        mul_le_mul_of_nonneg_right (by linarith) hlogu0
  have hprod0 : 0 ≤ log ((r : ℝ) * (|t| + 2)) *
      log (2 * log ((r : ℝ) * (|t| + 2))) := by
    have hb : log 2 ≤ log ((r : ℝ) * (|t| + 2)) :=
      log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
    exact mul_nonneg hell0 (log_nonneg (by linarith [log_two_gt_d9]))
  have hp := rpow_le_rpow hprod0 hprod (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hlograd : log (2 * (oddRad r : ℝ)) ≤ log (2 * (4 * log X) ^ 2) :=
    log_le_log (by positivity) (by nlinarith [sq_nonneg (log X)])
  unfold iwB
  dsimp
  nlinarith

/-- The quadratic odd radical consequence of the quoted Iwaniec region.
The conclusion is conditional only on that named region. P0045 page 6. -/
theorem nonreal_radical_growth (hiw : IwaniecZeroFree)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X P : ℝ, X0 ≤ X → PRange X P →
      ∀ z ∈ EZero X H T P, (∃ a, (z.2.1 a).im ≠ 0) →
        c * Lg X ^ 2 ≤ (oddRad z.1 : ℝ) := by
  have hHpos : 0 < H := by linarith
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1
    (logarithmic_error_isLittleO.bound (by positivity : (0 : ℝ) < 1 / (8 * H)))
  let V := max 1 (max (log (T + 2)) (U / 4))
  refine ⟨(log 2) ^ 2, exp V, by positivity, ?_⟩
  intro X P hX hP z hz hreal
  have hXpos : 0 < X := (exp_pos V).trans_le hX
  have hVX : V ≤ log X := by
    have hh := log_le_log (exp_pos V) hX
    simpa only [log_exp] using hh
  have hlog : 1 ≤ log X := (le_max_left _ _).trans hVX
  have hTX : log (T + 2) ≤ log X :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hVX)
  have hUX : U ≤ 4 * log X := by
    have hh : U / 4 ≤ log X := (le_max_right _ _).trans ((le_max_right _ _).trans hVX)
    linarith
  have hXone : 1 < X := by
    by_contra hh
    have hh' : log X ≤ 0 := log_nonpos hXpos.le (by linarith)
    linarith
  have hconstraint := nonreal_zero_constraint hiw hXone z hz hreal
  have hident : (log 2) ^ 2 * Lg X ^ 2 = (log X) ^ 2 := by
    unfold Lg
    rw [logb]
    field_simp
  rw [hident]
  by_contra hrad
  have hradle : (oddRad z.1 : ℝ) ≤ (log X) ^ 2 := le_of_lt (lt_of_not_ge hrad)
  have hB := iwB_le_logarithmic_error hz.1 hXpos hlog hT hTX hP.2 hz.2.1
    hz.2.2.2.2.2 hradle
  have hsmall := hU (4 * log X) hUX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 4 * log X)] at hsmall
  have hupper : 40000 * (log (2 * (4 * log X) ^ 2) +
      ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ)) ≤ log X / (2 * H) := by
    calc
      _ ≤ |40000 * (log (2 * (4 * log X) ^ 2) +
          ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ))| := le_abs_self _
      _ ≤ 1 / (8 * H) * (4 * log X) := hsmall
      _ = log X / (2 * H) := by field_simp <;> ring
  have hh := mul_le_mul_of_nonneg_left (hB.trans hupper) hHpos.le
  have he : H * (log X / (2 * H)) = log X / 2 := by field_simp <;> ring
  rw [he] at hh
  linarith

end LeanLab.LPZ2007.Iwaniec106

#print axioms LeanLab.LPZ2007.Iwaniec106.iwB_pos
#print axioms LeanLab.LPZ2007.Iwaniec106.nonreal_zero_constraint

#print axioms LeanLab.LPZ2007.Iwaniec106.logarithmic_error_isLittleO
#print axioms LeanLab.LPZ2007.Iwaniec106.iwB_le_logarithmic_error
#print axioms LeanLab.LPZ2007.Iwaniec106.nonreal_radical_growth
