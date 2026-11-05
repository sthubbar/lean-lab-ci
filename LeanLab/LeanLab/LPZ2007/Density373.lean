import LeanLab.LPZ2007.ZeroFamily373

/-!
Jutila 1977 page 46, Theorem 1 display 1.8, specialized with epsilon one half.
The analytic density estimate remains an explicit hypothesis.
The conversion to the exp of 4H bound quoted on P0045 page 5 is elementary.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Density373

open Real

/-- P0045 page 5, the density envelope quoted from Jutila.
At T at most P at most sqrt X, the exponent five halves yields exp of 4H. -/
theorem density_envelope_le {X H T P : ℝ} (hX : 1 < X) (hH : 0 ≤ H)
    (hT : 1 ≤ T) (hTP : T ≤ P) (hPX : P ≤ Real.sqrt X) :
    (P ^ 2 * T) ^ ((5 / 2 : ℝ) * (H / Real.log X)) ≤ Real.exp (4 * H) := by
  have hP : 0 < P := by linarith
  have hTpos : 0 < T := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hP2 : P ^ 2 ≤ X := by nlinarith [Real.sq_sqrt (by linarith : 0 ≤ X)]
  have hlogP : 2 * Real.log P ≤ Real.log X := by
    have h := Real.log_le_log (by positivity : 0 < P ^ 2) hP2
    simpa [Real.log_pow] using h
  have hlogT : Real.log T ≤ Real.log P := Real.log_le_log hTpos hTP
  have hbase : Real.log (P ^ 2 * T) ≤ (3 / 2 : ℝ) * Real.log X := by
    rw [Real.log_mul (by positivity : P ^ 2 ≠ 0) hTpos.ne', Real.log_pow]
    linarith
  rw [Real.rpow_def_of_pos (by positivity : 0 < P ^ 2 * T)]
  apply Real.exp_le_exp.2
  have hmul := mul_le_mul_of_nonneg_right hbase
    (by positivity : 0 ≤ (5 / 2 : ℝ) * (H / Real.log X))
  have he : ((3 / 2 : ℝ) * Real.log X) * ((5 / 2 : ℝ) * (H / Real.log X)) =
      (15 / 4 : ℝ) * H := by field_simp <;> ring
  rw [he] at hmul
  linarith

/-- Jutila 1977 page 46, the alpha range of Theorem 1.
For X at least exp of 5H, the exceptional strip starts in that range. -/
theorem density_parameter_range {X H : ℝ} (hH : 1 ≤ H)
    (hX : Real.exp (5 * H) ≤ X) :
    (4 / 5 : ℝ) ≤ 1 - H / Real.log X ∧ 1 - H / Real.log X ≤ 1 := by
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hlog : 5 * H ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hlogpos : 0 < Real.log X := by linarith
  constructor
  · have hdiv : H / Real.log X ≤ 1 / 5 := by
      rw [div_le_iff₀ hlogpos]
      linarith
    linarith
  · have hdiv : 0 ≤ H / Real.log X := by positivity
    linarith

/-- P0045 page 5, the quoted Jutila input, from Jutila 1977 page 46 display 1.8.
CONDITIONAL ON the displayed primitive rectangle density estimate at epsilon one half.
The count here is without multiplicity and is weaker than the published count. -/
theorem jutila_of_rectangle_density
    (hdensity : ∃ C : ℝ, 0 ≤ C ∧ ∀ α T P : ℝ,
      (4 / 5 : ℝ) ≤ α → α ≤ 1 → 1 ≤ T → T ≤ P →
        (({z : Σ r : ℕ, DirichletCharacter ℂ r × ℂ |
          1 ≤ z.1 ∧ (z.1 : ℝ) ≤ P ∧ z.2.1.IsPrimitive ∧ Lfun z.2.1 z.2.2 = 0 ∧
          α ≤ z.2.2.re ∧ z.2.2.re ≤ 1 ∧ |z.2.2.im| ≤ T}.ncard : ℕ) : ℝ) ≤
            C * (P ^ 2 * T) ^ ((5 / 2 : ℝ) * (1 - α))) : JutilaBound := by
  obtain ⟨C, hC, hD⟩ := hdensity
  refine ⟨C, ?_⟩
  intro H T hH hT
  refine ⟨Real.exp (5 * H), ?_⟩
  intro X P hX hTP hPX
  obtain ⟨hα0, hα1⟩ := density_parameter_range hH hX
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hlog : 5 * H ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hX
  have hXone : 1 < X := by
    by_contra h
    have hh := Real.log_nonpos hXp.le (le_of_not_gt h)
    linarith
  have hset : {z : Σ r : ℕ, DirichletCharacter ℂ r × ℂ |
      1 ≤ z.1 ∧ (z.1 : ℝ) ≤ P ∧ z.2.1.IsPrimitive ∧ Lfun z.2.1 z.2.2 = 0 ∧
      1 - H / Real.log X ≤ z.2.2.re ∧ z.2.2.re ≤ 1 ∧ |z.2.2.im| ≤ T} =
      EZero X H T P := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.2⟩
    · intro hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1,
        (ZeroFamily373.primitive_zero_re_lt_one hz.1 z.2.1 hz.2.2.1 hz.2.2.2.1).le,
        hz.2.2.2.2.2⟩
  have hcount := hD (1 - H / Real.log X) T P hα0 hα1 hT hTP
  rw [hset, show 1 - (1 - H / Real.log X) = H / Real.log X by ring] at hcount
  exact ⟨ZeroFamily373.EZero_finite X H T P, hcount.trans
    (mul_le_mul_of_nonneg_left (density_envelope_le hXone (by linarith) hT hTP hPX) hC)⟩

end LeanLab.LPZ2007.Density373

#print axioms LeanLab.LPZ2007.Density373.density_envelope_le
#print axioms LeanLab.LPZ2007.Density373.density_parameter_range
#print axioms LeanLab.LPZ2007.Density373.jutila_of_rectangle_density
