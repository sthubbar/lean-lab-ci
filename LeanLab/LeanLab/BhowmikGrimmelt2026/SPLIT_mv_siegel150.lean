/-
A split of the Siegel zero case of Theorem 5.1 into four leaves, plus an assembly that
combines them. The leaves are (1) the range of the Gallagher estimate at the dyadic point
`N = ⌊X⌋₊` with `R = X ^ ϑ`, (2) the weighted bound that follows from the Proposition 5.2
input, (3) the step from that weighted bound to the dyadic exceptional count, where the
uniform lower bound including proper prime powers is used, and (4) the absorption of the
factor `1 - β` and its logarithm into `1 / ϑ`.
AI wrote the Lean code.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp150b

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerSaving)
open ArithmeticFunction

/-! ### Private helpers for the range leaf -/

private lemma log_ge_inv_sq {ϑ X : ℝ} (hX : Real.exp (1 / ϑ ^ 2) ≤ X) :
    1 / ϑ ^ 2 ≤ Real.log X := by
  have h := Real.log_le_log (Real.exp_pos (1 / ϑ ^ 2)) hX
  rwa [Real.log_exp] at h

private lemma inv_sq_gt_twentyfive {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5) :
    (25 : ℝ) < 1 / ϑ ^ 2 := by
  rw [lt_div_iff₀ (by positivity : (0 : ℝ) < ϑ ^ 2)]
  nlinarith

private lemma exp_inv_sq_gt_two {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5) :
    (2 : ℝ) < Real.exp (1 / ϑ ^ 2) := by
  have h25 : (25 : ℝ) < 1 / ϑ ^ 2 := inv_sq_gt_twentyfive hϑ hϑ5
  have h1 : Real.exp 1 ≤ Real.exp (1 / ϑ ^ 2) := Real.exp_le_exp.mpr (by linarith)
  linarith [Real.exp_one_gt_d9]

private lemma sqrt_log_le_mul_log {ϑ X : ℝ} (hϑ : 0 < ϑ) (hXpos : 0 < X)
    (hlog : 1 / ϑ ^ 2 ≤ Real.log X) :
    Real.sqrt (Real.log X) ≤ ϑ * Real.log X := by
  have hlogpos : 0 < Real.log X := lt_of_lt_of_le (by positivity) hlog
  have hsq : (1 / ϑ) ^ 2 ≤ Real.log X := by
    have h : (1 / ϑ) ^ 2 = 1 / ϑ ^ 2 := by field_simp
    rwa [h]
  have hge : 1 / ϑ ≤ Real.sqrt (Real.log X) := Real.le_sqrt_of_sq_le hsq
  have h1 : 1 ≤ ϑ * Real.sqrt (Real.log X) := by
    have h := mul_le_mul_of_nonneg_left hge (le_of_lt hϑ)
    have h2 : ϑ * (1 / ϑ) = 1 := by field_simp
    linarith
  have h2 : Real.sqrt (Real.log X) ≤ (ϑ * Real.sqrt (Real.log X)) * Real.sqrt (Real.log X) :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) h1
  have h3 : (ϑ * Real.sqrt (Real.log X)) * Real.sqrt (Real.log X)
      = ϑ * Real.log X := by
    rw [mul_assoc, Real.mul_self_sqrt (le_of_lt hlogpos)]
  linarith

private lemma exp_sqrt_log_le_rpow {ϑ X : ℝ} (hϑ : 0 < ϑ) (hXpos : 0 < X)
    (hlog : 1 / ϑ ^ 2 ≤ Real.log X) :
    Real.exp (Real.sqrt (Real.log X)) ≤ X ^ ϑ := by
  have h2 := sqrt_log_le_mul_log hϑ hXpos hlog
  rw [Real.rpow_def_of_pos hXpos ϑ]
  exact Real.exp_le_exp.mpr (by linarith)

private lemma rpow_le_half {ϑ X : ℝ} (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5)
    (hXpos : 0 < X) (hlog : 1 / ϑ ^ 2 ≤ Real.log X) :
    X ^ ϑ ≤ X / 2 := by
  have h25 : (25 : ℝ) < 1 / ϑ ^ 2 := inv_sq_gt_twentyfive hϑ hϑ5
  have hlog2 : Real.log 2 ≤ (1 - ϑ) * Real.log X := by
    have h4 : (4 / 5 : ℝ) ≤ 1 - ϑ := by linarith
    have h1 : (1 / ϑ ^ 2) * (4 / 5) ≤ Real.log X * (1 - ϑ) :=
      mul_le_mul hlog h4 (by norm_num) (le_trans (by positivity) hlog)
    have h2 : (25 : ℝ) * (4 / 5) ≤ (1 / ϑ ^ 2) * (4 / 5) :=
      mul_le_mul_of_nonneg_right (le_of_lt h25) (by norm_num)
    have h3 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith
  have h2X : 2 * X ^ ϑ ≤ X := by
    have hmain : Real.exp (Real.log 2 + Real.log X * ϑ) ≤ Real.exp (Real.log X) :=
      Real.exp_le_exp.mpr (by linarith)
    calc 2 * X ^ ϑ = Real.exp (Real.log 2) * Real.exp (Real.log X * ϑ) := by
          rw [Real.exp_log (by norm_num), Real.rpow_def_of_pos hXpos ϑ]
      _ = Real.exp (Real.log 2 + Real.log X * ϑ) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Real.log X) := hmain
      _ = X := Real.exp_log hXpos
  linarith

/-- `Decidable` is a subsingleton, so the `if` of a proposition does not depend on which
decision procedure is used; this lets the spelled out `@ite ... Classical.propDecidable` of
the leaf statements be compared with the terms resolution puts into `Prop52`. -/
private lemma ite_decidable_canonical {α : Type*} {p : Prop} (d : Decidable p) (x y : α) :
    @ite α p d x y = @ite α p (Classical.propDecidable p) x y := by
  rw [Subsingleton.elim d (Classical.propDecidable p)]

private lemma two_le_floor {X : ℝ} (hX : 2 ≤ X) : 2 ≤ (⌊X⌋₊ : ℝ) := by
  have h : 2 ≤ ⌊X⌋₊ := Nat.le_floor hX
  have h' : ((2 : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := Nat.cast_le.mpr h
  simpa using h'

private lemma exp_sqrt_log_floor_two {X : ℝ} (hX : 2 ≤ X) :
    2 ≤ Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) := by
  have hN2 : 2 ≤ (⌊X⌋₊ : ℝ) := two_le_floor hX
  have h1 : Real.log 2 ≤ Real.log ⌊X⌋₊ := Real.log_le_log (by norm_num) hN2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsq : (Real.log 2) ^ 2 ≤ Real.log ⌊X⌋₊ := by
    have hstep : (Real.log 2) ^ 2 ≤ Real.log 2 := by nlinarith
    linarith
  have hs : Real.log 2 ≤ Real.sqrt (Real.log ⌊X⌋₊) := Real.le_sqrt_of_sq_le hsq
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) := Real.exp_le_exp.mpr hs

private lemma exp_sqrt_log_floor_rpow {ϑ X : ℝ} (hϑ : 0 < ϑ) (hXpos : 0 < X)
    (hlog : 1 / ϑ ^ 2 ≤ Real.log X) (hX2 : 2 ≤ X) :
    Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) ≤ X ^ ϑ := by
  have hN2 : 2 ≤ (⌊X⌋₊ : ℝ) := two_le_floor hX2
  have hNleX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hlogNle : Real.log ⌊X⌋₊ ≤ Real.log X := Real.log_le_log (by linarith) hNleX
  calc Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) ≤ Real.exp (Real.sqrt (Real.log X)) :=
        Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hlogNle)
    _ ≤ X ^ ϑ := exp_sqrt_log_le_rpow hϑ hXpos hlog

private lemma rpow_le_floor {ϑ X : ℝ} (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5) (hXpos : 0 < X)
    (hlog : 1 / ϑ ^ 2 ≤ Real.log X) (hX2 : 2 ≤ X) : X ^ ϑ ≤ (⌊X⌋₊ : ℝ) := by
  have hhalf : X ^ ϑ ≤ X / 2 := rpow_le_half hϑ hϑ5 hXpos hlog
  have hlt : X - 1 < (⌊X⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one X
    linarith
  linarith

/-- LEAF. Step 1, the range: for a fixed `ϑ` below one fifth the point `N = ⌊X⌋₊` with
`R = X ^ ϑ` is inside the range where the Gallagher estimate is available, both logarithms
are positive and both nodes are at least two, once `X` is large enough. -/
theorem siegel_range150 (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      2 ≤ Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) ∧
      Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) ≤ X ^ ϑ ∧
      X ^ ϑ ≤ (⌊X⌋₊ : ℝ) ∧
      (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) ∧ 2 ≤ X ∧
      0 < Real.log X ∧ 0 < Real.log (X ^ ϑ) := by
  refine ⟨Real.exp (1 / ϑ ^ 2), ?_⟩
  intro X hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hX2 : 2 ≤ X := le_of_lt (lt_of_lt_of_le (exp_inv_sq_gt_two hϑ hϑ5) hX)
  have hlog : 1 / ϑ ^ 2 ≤ Real.log X := log_ge_inv_sq hX
  have hlogpos : 0 < Real.log X := lt_of_lt_of_le (by positivity) hlog
  exact ⟨exp_sqrt_log_floor_two hX2,
    exp_sqrt_log_floor_rpow hϑ hXpos hlog hX2,
    rpow_le_floor hϑ hϑ5 hXpos hlog hX2,
    two_le_floor hX2, hX2, hlogpos, by
      rw [Real.log_rpow hXpos ϑ]
      exact mul_pos hϑ hlogpos⟩

/-- LEAF. Step 2, the weighted bound: part two of the Proposition 5.2 input, specialised to
`N = ⌊X⌋₊` and `R = X ^ ϑ`, with the factor `1 - β` and its logarithm retained, and only the
range of step 1 assumed. The decidable instances are written out because the source file
makes them local instances. -/
theorem siegel_upper150 (h52 : Prop52) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X ϑ : ℝ), 2 ≤ X → 0 < ϑ → ϑ < 1 / 5 →
        2 ≤ Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) →
        Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) ≤ X ^ ϑ →
        X ^ ϑ ≤ (⌊X⌋₊ : ℝ) →
        ∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ),
          SiegelZero (X ^ ϑ) r₀ χ₀ β →
          primSum (X ^ ϑ)           (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) ≤
            C * (1 - β) * Real.log ⌊X⌋₊ *
              Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) := by
  obtain ⟨c, hc, C, hP⟩ := h52
  refine ⟨c, max C 1, hc, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro X ϑ hX2 hϑ hϑ5 h1 h2 h3 r₀ hr₀ χ₀ β hS
  have hmain := ((hP ⌊X⌋₊ (X ^ ϑ) h1 h2 h3).2 r₀ χ₀ β hS)
  have hβlt : β < 1 := hS.2.2.2.2.1
  have hN1 : (1 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    have hx1 : (1 : ℝ) ≤ X ^ ϑ := Real.one_le_rpow (by linarith) (le_of_lt hϑ)
    linarith
  have hlogN : 0 ≤ Real.log ⌊X⌋₊ := Real.log_nonneg hN1
  have hK0 : 0 ≤ (1 - β) * Real.log ⌊X⌋₊ *
      Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) :=
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) hlogN)
      (le_of_lt (Real.exp_pos _))
  calc primSum (X ^ ϑ) (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
        (fun n => (vonMangoldt n : ℂ) * χ n -
            @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
          @ite ℂ (r = r₀ ∧ HEq χ χ₀)
            (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0))
      ≤ C * (1 - β) * Real.log ⌊X⌋₊ *
          Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) := by
        simpa only [ite_decidable_canonical, neg_mul] using hmain
    _ = C * ((1 - β) * Real.log ⌊X⌋₊ *
          Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ))) := by ring
    _ ≤ max C 1 * ((1 - β) * Real.log ⌊X⌋₊ *
          Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ))) :=
        mul_le_mul_of_nonneg_right (le_max_left C 1) hK0
    _ = max C 1 * (1 - β) * Real.log ⌊X⌋₊ *
          Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) := by ring

/-- LEAF. Step 3, the count from the weighted bound: each even `N` in `[X/2, X]` which fails
to be a sum of two primes contributes at least a fixed multiple of `log X / X` to the
weighted sum of step 2, uniformly in the Siegel data. This is where the uniform lower bound
for the main term, proper prime powers included, is used. -/
theorem siegel_count150 (hGallagher : GallagherStandard) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X ϑ : ℝ), 2 ≤ X → 0 < ϑ → ϑ < 1 / 5 →
        ∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ),
          SiegelZero (X ^ ϑ) r₀ χ₀ β →
          (Edy X : ℝ) ≤ C * primSum (X ^ ϑ)           (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) := by
  sorry

/-- LEAF. Step 4, the scalar absorption: the factor `1 - β` against its own logarithm is at
most `1 / ϑ`, since a Siegel zero at level `X ^ ϑ` gives `1 - β ≤ 1 / log (X ^ ϑ)` and
`log ⌊X⌋₊ ≤ log X`. -/
theorem siegel_absorb150 (X ϑ β : ℝ) (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5) (hX : 2 ≤ X)
    (hβlow : 1 - 1 / Real.log (X ^ ϑ) < β) (hβlt : β < 1) :
    (1 - β) * Real.log ⌊X⌋₊ ≤ 1 / ϑ := by
  have hXpos : 0 < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hlogR : Real.log (X ^ ϑ) = ϑ * Real.log X := Real.log_rpow hXpos ϑ
  have hlogRpos : 0 < Real.log (X ^ ϑ) := by
    rw [hlogR]
    exact mul_pos hϑ hlogX
  have hβnn : 0 < 1 - β := by linarith
  have hlt : 1 - β < 1 / Real.log (X ^ ϑ) := by linarith
  have hkey : (1 - β) * Real.log (X ^ ϑ) < 1 := by
    have h := mul_lt_mul_of_pos_right hlt hlogRpos
    rwa [one_div_mul_cancel (ne_of_gt hlogRpos)] at h
  have hstep : ϑ * ((1 - β) * Real.log X) = (1 - β) * Real.log (X ^ ϑ) := by
    rw [hlogR]; ring
  have h3 : (1 - β) * Real.log X ≤ 1 / ϑ := by
    rw [le_div_iff₀ hϑ]
    linarith
  have hN2 : (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one X
    have h2 : (1 : ℝ) < (⌊X⌋₊ : ℝ) := by linarith
    have h3 : (1 : ℕ) < ⌊X⌋₊ := by exact_mod_cast h2
    exact_mod_cast (by omega : (2 : ℕ) ≤ ⌊X⌋₊)
  have hlogNle : Real.log ⌊X⌋₊ ≤ Real.log X :=
    Real.log_le_log (by linarith) (Nat.floor_le (le_of_lt hXpos))
  calc (1 - β) * Real.log ⌊X⌋₊ ≤ (1 - β) * Real.log X :=
        mul_le_mul_of_nonneg_left hlogNle (le_of_lt hβnn)
    _ ≤ 1 / ϑ := h3

/-- The Siegel zero case of Theorem 5.1, assembled from the four leaves above. -/
theorem mv_siegel150_split (h52 : Prop52) (hGallagher : GallagherStandard) :
    ∃ ϑ₀ : ℝ, 0 < ϑ₀ ∧ ∀ ϑ : ℝ, 0 < ϑ → ϑ < ϑ₀ → ϑ < 1 / 5 →
      ∃ C X₀ : ℝ, ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
        (∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
          SiegelZero (X ^ ϑ) r χ β) →
        (Edy X : ℝ) ≤ C * X ^ (1 - ϑ / 2) := by
  obtain ⟨c, C₂, hc, hC₂, hP⟩ := siegel_upper150 h52
  obtain ⟨C₁, hC₁, hcount⟩ := siegel_count150 hGallagher
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro ϑ hϑ _hϑlt hϑ5
  obtain ⟨Xr, hXr⟩ := siegel_range150 ϑ hϑ hϑ5
  refine ⟨C₁ * C₂ / ϑ, Xr, ?_⟩
  intro X hX2 hX hsig
  obtain ⟨r₀, hr₀, χ₀, β, hS⟩ := hsig
  haveI : NeZero r₀ := hr₀
  obtain ⟨h1, h2, h3, hN2, _hX2', hlogX, hlogR⟩ := hXr X hX
  have hSc := hS
  obtain ⟨-, -, -, hβlow, hβlt, -⟩ := hSc
  have hXpos : 0 < X := by linarith
  have hlogNnn : 0 ≤ Real.log ⌊X⌋₊ := by
    have hle : Real.log 2 ≤ Real.log ⌊X⌋₊ := Real.log_le_log (by norm_num) hN2
    have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have h1βnn : 0 ≤ 1 - β := by linarith
  have hE0 : -(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ) ≤ 0 := by
    have hpos : 0 ≤ (c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ) :=
      div_nonneg (by positivity) (le_of_lt hlogR)
    have hneg : -(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)
        = -((c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) := neg_div _ _
    rw [hneg]
    linarith
  have hexp1 : Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hE0
  have hub :
      primSum (X ^ ϑ)         (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
              (fun n => (vonMangoldt n : ℂ) * χ n -
                  @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                  (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) ≤
      C₂ * (1 - β) * Real.log ⌊X⌋₊ *
        Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) :=
    hP X ϑ hX2 hϑ hϑ5 h1 h2 h3 r₀ χ₀ β hS
  have hbr :
      (Edy X : ℝ) ≤ C₁ * primSum (X ^ ϑ)           (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) :=
    hcount X ϑ hX2 hϑ hϑ5 r₀ χ₀ β hS
  have hmul :
      C₁ * primSum (X ^ ϑ)           (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) ≤
      C₁ * (C₂ * (1 - β) * Real.log ⌊X⌋₊ *
        Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ))) :=
    mul_le_mul_of_nonneg_left hub (le_of_lt hC₁)
  have hscalar :
      C₂ * (1 - β) * Real.log ⌊X⌋₊ *
        Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) ≤ C₂ * (1 / ϑ) := by
    have hstep :
        C₂ * (1 - β) * Real.log ⌊X⌋₊ *
          Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) ≤
        C₂ * (1 - β) * Real.log ⌊X⌋₊ * 1 := by
      refine mul_le_mul_of_nonneg_left hexp1 ?_
      exact mul_nonneg (mul_nonneg (le_of_lt hC₂) h1βnn) hlogNnn
    have hβ : (1 - β) * Real.log ⌊X⌋₊ ≤ 1 / ϑ :=
      siegel_absorb150 X ϑ β hϑ hϑ5 hX2 hβlow hβlt
    have hβ' : C₂ * ((1 - β) * Real.log ⌊X⌋₊) ≤ C₂ * (1 / ϑ) :=
      mul_le_mul_of_nonneg_left hβ (le_of_lt hC₂)
    calc C₂ * (1 - β) * Real.log ⌊X⌋₊ *
          Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ))
        ≤ C₂ * (1 - β) * Real.log ⌊X⌋₊ * 1 := hstep
      _ = C₂ * ((1 - β) * Real.log ⌊X⌋₊) := by ring
      _ ≤ C₂ * (1 / ϑ) := hβ'
  refine (hbr.trans (hmul.trans
    (mul_le_mul_of_nonneg_left hscalar (le_of_lt hC₁)))).trans ?_
  have hone : (1 : ℝ) ≤ X ^ (1 - ϑ / 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hnn : (0 : ℝ) ≤ C₁ * (C₂ * (1 / ϑ)) := by
    have h2 : (0 : ℝ) < C₂ * (1 / ϑ) := mul_pos hC₂ (one_div_pos.mpr hϑ)
    exact mul_nonneg (le_of_lt hC₁) (le_of_lt h2)
  calc C₁ * (C₂ * (1 / ϑ)) ≤ C₁ * (C₂ * (1 / ϑ)) * X ^ (1 - ϑ / 2) :=
        le_mul_of_one_le_right hnn hone
    _ = C₁ * C₂ / ϑ * X ^ (1 - ϑ / 2) := by ring

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.mv_siegel150_split
