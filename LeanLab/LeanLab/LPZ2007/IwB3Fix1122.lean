import LeanLab.LPZ2007.Decomp106
import LeanLab.LPZ2007.LogRadical407

/-!
UNIT P1122-0002, REPAIR of the Iwaniec denominator.

Iwaniec 1974, Inventiones math. 23, page 97, defines `l = log q(|t| + 3)` and
`ϑ⁻¹ = 4·10⁴ (log d + (l log 2l)^{3/4})`, and Theorem 2 there gives the zero free region
`Re ρ > 1 - ϑ` for every non real character mod `q`.
P0045, journal page 775, quotes this with `ℓ = log(r(|t| + 2))`, and the lab definition `iwB`
in `Statements.lean` follows the P0045 misquote.

Since `iwB r t ≤ iwB3 r t`, the region `Re s > 1 - 1/iwB` is LARGER than the region
`Re s > 1 - 1/iwB3`. So `IwaniecZeroFree` is the STRONGER statement, stronger than the source
supports, and `IwaniecZeroFree3` below is the one that Iwaniec 1974 page 97 supports.
`iwB` and `IwaniecZeroFree` are not edited here. Every dependent of `IwaniecZeroFree` in this
folder is reproved below from `IwaniecZeroFree3`, with the suffix 1122.

AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.IwB3Fix1122

open Real Filter Asymptotics Eq14FromCor42

/-- Iwaniec 1974 page 97, the display before Theorem 1: the denominator
`ϑ⁻¹ = 4·10⁴ (log d + (l log 2l)^{3/4})` with `l = log q(|t| + 3)`.
This is `iwB` of `Statements.lean` with `|t| + 3` in place of the `|t| + 2` printed on
P0045 journal page 775. As in `iwB`, `log d` is replaced by the larger `log(2 r')` of P0045,
`r'` the odd radical; that change only weakens the region. -/
noncomputable def iwB3 (r : ℕ) (t : ℝ) : ℝ :=
  let ℓ := Real.log (r * (|t| + 3))
  4 * 10 ^ 4 * (Real.log (2 * oddRad r) + (ℓ * Real.log (2 * ℓ)) ^ (3 / 4 : ℝ))

/-- Iwaniec 1974 page 97, Theorem 2, in the shape quoted on P0045 journal page 775 but with
the denominator `iwB3` that the source prints: for a non real primitive `χ` mod `r`,
`L(s, χ)` has no zero with `Re s > 1 - 1/iwB3`. Weaker than `IwaniecZeroFree`. -/
def IwaniecZeroFree3 : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → (∃ a, (χ a).im ≠ 0) →
    ∀ s : ℂ, 1 - 1 / iwB3 r s.im < s.re → Lfun χ s ≠ 0

/-- Comparison of the P0045 page 775 denominator with the Iwaniec 1974 page 97 denominator:
the misquoted `|t| + 2` version is the smaller one, for every modulus `r ≥ 1` and every `t`.
No further side condition is needed, since `ℓ ≥ log 2 > 1/2` puts both logs in the range
where `ℓ log(2ℓ)` is monotone. -/
theorem iwB_le_iwB3 {r : ℕ} (hr : 1 ≤ r) (t : ℝ) : iwB r t ≤ iwB3 r t := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h2 : (2 : ℝ) ≤ r * (|t| + 2) := by nlinarith [abs_nonneg t]
  have h23 : (r : ℝ) * (|t| + 2) ≤ r * (|t| + 3) := by nlinarith
  have ha2 : log 2 ≤ log ((r : ℝ) * (|t| + 2)) := log_le_log (by norm_num) h2
  have hab : log ((r : ℝ) * (|t| + 2)) ≤ log ((r : ℝ) * (|t| + 3)) :=
    log_le_log (by linarith) h23
  have hl2 := log_two_gt_d9
  have ha0 : 0 < log ((r : ℝ) * (|t| + 2)) := by linarith
  have hla0 : 0 ≤ log (2 * log ((r : ℝ) * (|t| + 2))) := log_nonneg (by linarith)
  have hlab : log (2 * log ((r : ℝ) * (|t| + 2))) ≤ log (2 * log ((r : ℝ) * (|t| + 3))) :=
    log_le_log (by positivity) (by linarith)
  have hprod : log ((r : ℝ) * (|t| + 2)) * log (2 * log ((r : ℝ) * (|t| + 2))) ≤
      log ((r : ℝ) * (|t| + 3)) * log (2 * log ((r : ℝ) * (|t| + 3))) :=
    mul_le_mul hab hlab hla0 (by linarith)
  have hp := rpow_le_rpow (mul_nonneg ha0.le hla0) hprod (by norm_num : (0 : ℝ) ≤ 3 / 4)
  unfold iwB iwB3
  dsimp
  nlinarith

/-- The Iwaniec 1974 page 97 denominator is positive. -/
theorem iwB3_pos {r : ℕ} (hr : 1 ≤ r) (t : ℝ) : 0 < iwB3 r t :=
  (Iwaniec106.iwB_pos hr t).trans_le (iwB_le_iwB3 hr t)

/-- The lab input `IwaniecZeroFree`, which follows the `|t| + 2` printed on P0045 page 775,
implies the statement `IwaniecZeroFree3` that Iwaniec 1974 page 97 supports.
So the old input is the stronger one. The converse is not claimed. -/
theorem zeroFree3_of_zeroFree (h : IwaniecZeroFree) : IwaniecZeroFree3 := by
  intro r hr χ hprim hnr s hs
  apply h r hr χ hprim hnr s
  have hle := one_div_le_one_div_of_le (Iwaniec106.iwB_pos hr s.im) (iwB_le_iwB3 hr s.im)
  linarith

/-- `Iwaniec106.nonreal_zero_constraint` from the corrected region.
P0045 journal page 775 with Iwaniec 1974 page 97. -/
theorem nonreal_zero_constraint1122 (hiw : IwaniecZeroFree3)
    {X H T P : ℝ} (hX : 1 < X)
    (z : Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (hz : z ∈ EZero X H T P) (hreal : ∃ a, (z.2.1 a).im ≠ 0) :
    log X ≤ H * iwB3 z.1 z.2.2.im := by
  have hB := iwB3_pos hz.1 z.2.2.im
  have hlog := log_pos hX
  have hupper : z.2.2.re ≤ 1 - 1 / iwB3 z.1 z.2.2.im := by
    by_contra h
    have hlt : 1 - 1 / iwB3 z.1 z.2.2.im < z.2.2.re := by linarith
    exact hiw z.1 hz.1 z.2.1 hz.2.2.1 hreal z.2.2 hlt hz.2.2.2.1
  have hnear := hz.2.2.2.2.1
  have hdiv : 1 / iwB3 z.1 z.2.2.im ≤ H / log X := by linarith
  have hh := (div_le_div_iff₀ hB hlog).mp hdiv
  simpa only [one_mul] using hh

/-- `LogRadical407.denominator_majorant` for the corrected denominator.
The only change in the hypotheses is `log (T + 3) ≤ log X` in place of `log (T + 2) ≤ log X`. -/
theorem denominator_majorant1122 {X P T : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hXpos : 0 < X) (hX : 1 ≤ log X) (hT : 1 ≤ T) (hTX : log (T + 3) ≤ log X)
    (hXP : P ≤ X ^ (0.41 : ℝ)) (hrP : (r : ℝ) ≤ P)
    {t : ℝ} (ht : |t| ≤ T) :
    iwB3 r t ≤ 40000 * log (2 * (oddRad r : ℝ)) +
      40000 * (log (2 * (4 * log X) ^ 2) +
        ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hargpos : 0 < (r : ℝ) * (|t| + 3) := by positivity
  have hargle : (r : ℝ) * (|t| + 3) ≤ X ^ (0.41 : ℝ) * (T + 3) :=
    mul_le_mul (hrP.trans hXP) (by linarith) (by positivity) (by positivity)
  have hell : log ((r : ℝ) * (|t| + 3)) ≤ 2 * log X := by
    have hh := log_le_log hargpos hargle
    rw [log_mul (by positivity : (X ^ (0.41 : ℝ)) ≠ 0)
      (by linarith : T + 3 ≠ 0), log_rpow hXpos] at hh
    linarith
  have hellLower : log 2 ≤ log ((r : ℝ) * (|t| + 3)) :=
    log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  have hell0 : 0 < log ((r : ℝ) * (|t| + 3)) :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hellLower
  have hlogell : log (2 * log ((r : ℝ) * (|t| + 3))) ≤ log (4 * log X) :=
    log_le_log (by positivity) (by linarith)
  have hlogu0 : 0 ≤ log (4 * log X) := log_nonneg (by linarith)
  have hprod : log ((r : ℝ) * (|t| + 3)) *
      log (2 * log ((r : ℝ) * (|t| + 3))) ≤ (4 * log X) * log (4 * log X) := by
    calc
      _ ≤ log ((r : ℝ) * (|t| + 3)) * log (4 * log X) :=
        mul_le_mul_of_nonneg_left hlogell hell0.le
      _ ≤ (4 * log X) * log (4 * log X) :=
        mul_le_mul_of_nonneg_right (by linarith) hlogu0
  have hprod0 : 0 ≤ log ((r : ℝ) * (|t| + 3)) *
      log (2 * log ((r : ℝ) * (|t| + 3))) := by
    exact mul_nonneg hell0.le (log_nonneg (by linarith [log_two_gt_d9]))
  have hp := rpow_le_rpow hprod0 hprod (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hlogextra : 0 ≤ log (2 * (4 * log X) ^ 2) := log_nonneg (by nlinarith)
  unfold iwB3
  dsimp
  nlinarith

/-- `Iwaniec106.iwB_le_logarithmic_error` for the corrected denominator, a small odd radical
gives a sublinear majorant, here with a harmless factor 2. Hypothesis `log (T + 3) ≤ log X` replaces `log (T + 2) ≤ log X`. -/
theorem iwB3_le_logarithmic_error1122 {X P T : ℝ} {r : ℕ} (hr : 1 ≤ r)
    (hXpos : 0 < X) (hX : 1 ≤ log X) (hT : 1 ≤ T) (hTX : log (T + 3) ≤ log X)
    (hXP : P ≤ X ^ (0.41 : ℝ)) (hrP : (r : ℝ) ≤ P)
    {t : ℝ} (ht : |t| ≤ T) (hrad : (oddRad r : ℝ) ≤ (log X) ^ 2) :
    iwB3 r t ≤ 2 * (40000 * (log (2 * (4 * log X) ^ 2) +
      ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ))) := by
  have hmaj := denominator_majorant1122 hr hXpos hX hT hTX hXP hrP ht
  have hradpos : (0 : ℝ) < oddRad r := by exact_mod_cast oddRad_pos r
  have hlograd : log (2 * (oddRad r : ℝ)) ≤ log (2 * (4 * log X) ^ 2) :=
    log_le_log (by positivity) (by nlinarith [sq_nonneg (log X)])
  have hextra : 0 ≤ log (2 * (4 * log X) ^ 2) := log_nonneg (by nlinarith)
  have hpw : 0 ≤ ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ) :=
    rpow_nonneg (mul_nonneg (by linarith) (log_nonneg (by linarith))) _
  nlinarith

/-- `LogRadical407.nonreal_log_radical_growth` from the corrected region: P0045 journal
page 775, last paragraph of the proof of Corollary 4.2, `log r' ≫ L` for non real
exceptional characters. CONDITIONAL ON `IwaniecZeroFree3` only, which is what
Iwaniec 1974 page 97 Theorem 2 supports. -/
theorem nonreal_log_radical_growth1122 (hiw : IwaniecZeroFree3)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X P : ℝ, X0 ≤ X → PRange X P →
      ∀ z ∈ EZero X H T P, (∃ a, (z.2.1 a).im ≠ 0) →
        c * Lg X ≤ log (oddRad z.1 : ℝ) := by
  have hHpos : 0 < H := by linarith
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1
    (Iwaniec106.logarithmic_error_isLittleO.bound
      (by positivity : (0 : ℝ) < 1 / (8 * H)))
  let V := max 1 (max (log (T + 3)) (max (U / 4) (160000 * H * log 2)))
  refine ⟨log 2 / (160000 * H), exp V, by positivity, ?_⟩
  intro X P hX hP z hz hreal
  have hXpos : 0 < X := (exp_pos V).trans_le hX
  have hVX : V ≤ log X := by
    have hh := log_le_log (exp_pos V) hX
    simpa only [log_exp] using hh
  have hlog : 1 ≤ log X := (le_max_left _ _).trans hVX
  have hTX : log (T + 3) ≤ log X :=
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
  have hconstraint := nonreal_zero_constraint1122 hiw hXone z hz hreal
  have hB := denominator_majorant1122 hz.1 hXpos hlog hT hTX hP.2 hz.2.1 hz.2.2.2.2.2
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

/-- `Iwaniec106.nonreal_radical_growth` and `Decomp106.nonreal_exceptional_radical` from the
corrected region: the quadratic bound `r' ≫ L²` of display (10), P0045 journal page 775,
for non real exceptional characters. CONDITIONAL ON `IwaniecZeroFree3` only. -/
theorem nonreal_radical_growth1122 (hiw : IwaniecZeroFree3)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X P : ℝ, X0 ≤ X → PRange X P →
      ∀ z ∈ EZero X H T P, (∃ a, (z.2.1 a).im ≠ 0) →
        c * Lg X ^ 2 ≤ (oddRad z.1 : ℝ) := by
  have hHpos : 0 < H := by linarith
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1
    (Iwaniec106.logarithmic_error_isLittleO.bound (by positivity : (0 : ℝ) < 1 / (16 * H)))
  let V := max 1 (max (log (T + 3)) (U / 4))
  refine ⟨(log 2) ^ 2, exp V, by positivity, ?_⟩
  intro X P hX hP z hz hreal
  have hXpos : 0 < X := (exp_pos V).trans_le hX
  have hVX : V ≤ log X := by
    have hh := log_le_log (exp_pos V) hX
    simpa only [log_exp] using hh
  have hlog : 1 ≤ log X := (le_max_left _ _).trans hVX
  have hTX : log (T + 3) ≤ log X :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hVX)
  have hUX : U ≤ 4 * log X := by
    have hh : U / 4 ≤ log X := (le_max_right _ _).trans ((le_max_right _ _).trans hVX)
    linarith
  have hXone : 1 < X := by
    by_contra hh
    have hh' : log X ≤ 0 := log_nonpos hXpos.le (by linarith)
    linarith
  have hconstraint := nonreal_zero_constraint1122 hiw hXone z hz hreal
  have hident : (log 2) ^ 2 * Lg X ^ 2 = (log X) ^ 2 := by
    unfold Lg
    rw [logb]
    field_simp
  rw [hident]
  by_contra hrad
  have hradle : (oddRad z.1 : ℝ) ≤ (log X) ^ 2 := le_of_lt (lt_of_not_ge hrad)
  have hB := iwB3_le_logarithmic_error1122 hz.1 hXpos hlog hT hTX hP.2 hz.2.1
    hz.2.2.2.2.2 hradle
  have hsmall := hU (4 * log X) hUX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 4 * log X)] at hsmall
  have hE : 40000 * (log (2 * (4 * log X) ^ 2) +
      ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ)) ≤ log X / (4 * H) := by
    calc
      _ ≤ |40000 * (log (2 * (4 * log X) ^ 2) +
          ((4 * log X) * log (4 * log X)) ^ (3 / 4 : ℝ))| := le_abs_self _
      _ ≤ 1 / (16 * H) * (4 * log X) := hsmall
      _ = log X / (4 * H) := by field_simp <;> ring
  have hupper : iwB3 z.1 z.2.2.im ≤ 2 * (log X / (4 * H)) := by linarith
  have hh := mul_le_mul_of_nonneg_left hupper hHpos.le
  have he : H * (2 * (log X / (4 * H))) = log X / 2 := by field_simp <;> ring
  rw [he] at hh
  linarith

/-- `Decomp106.exceptional_radical` from the corrected region: the assembly of the real and
the non real case in the proof of display (10), P0045 journal page 775.
CONDITIONAL ON the Davenport classification, the real zero bound and `IwaniecZeroFree3`. -/
theorem exceptional_radical1122 (hclass : RealPrimitiveModulus)
    (hzero : RealZeroBound) (hiw : IwaniecZeroFree3)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X P : ℝ, X0 ≤ X → PRange X P →
      ∀ z ∈ EZero X H T P, c * Lg X ^ 2 ≤ (oddRad z.1 : ℝ) := by
  classical
  obtain ⟨cr, Xr, hcr, hr⟩ := Decomp106.real_exceptional_conductor hzero H T hH hT
  obtain ⟨cn, Xn, hcn, hn⟩ := nonreal_radical_growth1122 hiw H T hH hT
  refine ⟨min (cr / 8) cn, max Xr Xn, lt_min (by positivity) hcn, ?_⟩
  intro X P hX hP z hz
  by_cases hreal : ∀ a, (z.2.1 a).im = 0
  · have hc := hr X P (le_trans (le_max_left _ _) hX) hP z hz hreal
    have ht := Decomp106.real_radical_transfer hclass hz.1 z.2.1 hz.2.2.1 hreal hc
    have hm := mul_le_mul_of_nonneg_right (min_le_left (cr / 8) cn) (sq_nonneg (Lg X))
    calc
      min (cr / 8) cn * Lg X ^ 2 ≤ cr / 8 * Lg X ^ 2 := hm
      _ = (cr * Lg X ^ 2) / 8 := by ring
      _ ≤ (oddRad z.1 : ℝ) := ht
  · have hex : ∃ a, (z.2.1 a).im ≠ 0 := by simpa only [not_forall] using hreal
    exact le_trans
      (mul_le_mul_of_nonneg_right (min_le_right (cr / 8) cn) (sq_nonneg (Lg X)))
      (hn X P (le_trans (le_max_right _ _) hX) hP z hz hex)

end LeanLab.LPZ2007.IwB3Fix1122

#print axioms LeanLab.LPZ2007.IwB3Fix1122.iwB_le_iwB3
#print axioms LeanLab.LPZ2007.IwB3Fix1122.iwB3_pos
#print axioms LeanLab.LPZ2007.IwB3Fix1122.zeroFree3_of_zeroFree
#print axioms LeanLab.LPZ2007.IwB3Fix1122.nonreal_zero_constraint1122
#print axioms LeanLab.LPZ2007.IwB3Fix1122.denominator_majorant1122
#print axioms LeanLab.LPZ2007.IwB3Fix1122.iwB3_le_logarithmic_error1122
#print axioms LeanLab.LPZ2007.IwB3Fix1122.nonreal_log_radical_growth1122
#print axioms LeanLab.LPZ2007.IwB3Fix1122.nonreal_radical_growth1122
#print axioms LeanLab.LPZ2007.IwB3Fix1122.exceptional_radical1122
