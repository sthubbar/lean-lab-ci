/-
P0069 Baker Harman Pintz 1997, page 19. Elementary exceptional set count bookkeeping.
Prachar and Montgomery zero estimates remain inputs. No zero estimate is proved here.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
namespace LeanLab.BHP1997.Task670ExceptionalCount
open Filter Asymptotics
open scoped Topology
/-- P0069 page 19. The sublinear density exponent and every log loss are eventually
absorbed by half the exponent four fifths. -/
theorem eventually_exceptional_exponent (ε A : ℝ) : ∀ᶠ L : ℝ in atTop,
    7 * ε * L ^ (1 / 5 : ℝ) + 2 * A * Real.log L ≤ L ^ (4 / 5 : ℝ) / 2 := by
  let D : ℝ := |7 * ε| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hp : ∀ᶠ L : ℝ in atTop, L ^ (-(3 / 5 : ℝ)) ≤ 1 / (4 * D) :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 5)).eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (4 * D)))).mono fun _ h => h.le
  have hl := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).const_mul_left
    (2 * A)).bound (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hp, hl, eventually_gt_atTop (0 : ℝ)] with L hLp hLl hL
  have he : L ^ (1 / 5 : ℝ) = L ^ (4 / 5 : ℝ) * L ^ (-(3 / 5 : ℝ)) := by
    rw [← Real.rpow_add hL]; norm_num
  have hpow : D * L ^ (1 / 5 : ℝ) ≤ L ^ (4 / 5 : ℝ) / 4 := by
    rw [he]
    calc
      _ ≤ D * (L ^ (4 / 5 : ℝ) * (1 / (4 * D))) := by gcongr
      _ = _ := by field_simp
  have hlog : 2 * A * Real.log L ≤ L ^ (4 / 5 : ℝ) / 4 := by
    have := (le_abs_self (2 * A * Real.log L)).trans hLl
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le _), div_eq_mul_inv, mul_comm, one_mul] using this
  have hcoef : 7 * ε * L ^ (1 / 5 : ℝ) ≤ D * L ^ (1 / 5 : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
    dsimp [D]; linarith [le_abs_self (7 * ε)]
  linarith
/-- P0069 page 19. The displayed exponential exceptional count has the required
square root modulus saving when the modulus exceeds exp of L to four fifths. -/
theorem eventually_large_modulus_scale (ε A : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, Real.exp (L ^ (4 / 5 : ℝ)) ≤ q →
      Real.exp (7 * ε * L ^ (1 / 5 : ℝ)) ≤ q ^ (1 / 2 : ℝ) * L ^ (-2 * A) := by
  filter_upwards [eventually_exceptional_exponent ε A, eventually_gt_atTop (0 : ℝ)] with L hLexp hL
  intro q hq
  have hq0 : 0 < q := (Real.exp_pos _).trans_le hq
  have hlogq : L ^ (4 / 5 : ℝ) ≤ Real.log q := by
    have hh := Real.log_le_log (Real.exp_pos _) hq
    simpa only [Real.log_exp] using hh
  rw [Real.rpow_def_of_pos hq0 (1 / 2), Real.rpow_def_of_pos hL (-2 * A), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- P0069 page 19. A finite set with the displayed zero density cardinality bound
inherits the square root modulus bound. The zero density estimate remains a premise. -/
theorem eventually_large_modulus_card {α : Type*} (ε A : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ q K : ℝ, 0 ≤ K → Real.exp (L ^ (4 / 5 : ℝ)) ≤ q →
      ∀ E : Finset α, (E.card : ℝ) ≤ K * Real.exp (7 * ε * L ^ (1 / 5 : ℝ)) →
        (E.card : ℝ) ≤ K * q ^ (1 / 2 : ℝ) * L ^ (-2 * A) := by
  filter_upwards [eventually_large_modulus_scale ε A] with L hL
  intro q K hK hq E hE
  exact hE.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hL q hq) hK)

/-- P0069 page 19 with its free exponent replaced by twice A. An exceptional set
of size at most one has the desired count when q is at least L to four A. -/
theorem middle_modulus_card {α : Type*} {L q A : ℝ} (hL : 0 < L)
    (hq : L ^ (4 * A) ≤ q) (E : Finset α) (hE : E.card ≤ 1) :
    (E.card : ℝ) ≤ q ^ (1 / 2 : ℝ) * L ^ (-2 * A) := by
  have hhalf := Real.rpow_le_rpow (Real.rpow_nonneg hL.le (4 * A)) hq
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he : (L ^ (4 * A)) ^ (1 / 2 : ℝ) = L ^ (2 * A) := by
    rw [← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [he] at hhalf
  have hprod := mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hL.le (-2 * A))
  have he1 : L ^ (2 * A) * L ^ (-2 * A) = 1 := by
    rw [← Real.rpow_add hL]
    simp
  rw [he1] at hprod
  exact (by exact_mod_cast hE : (E.card : ℝ) ≤ 1).trans hprod

end LeanLab.BHP1997.Task670ExceptionalCount
