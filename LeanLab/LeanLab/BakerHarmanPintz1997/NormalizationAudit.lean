/-
P0069, pages 1 and 24, the normalization QUESTION, settled by U-1617.
The interval I has width 2Y and the old equation 4.2 used Y/y1. Audit1617.lean refutes the old
Lemma11. This file keeps the name of the old diagnostic, states it for the old predicate, and
gives what the repaired predicate needs: a vacuity instance, the sum over I with its true factor,
and the incompatibility of the two forms at positive density.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Audit1617
import LeanLab.BakerHarmanPintz1997.DecompBounds
open Finset
namespace LeanLab.BakerHarmanPintz1997
open LeanLab.BakerHarmanPintz1997.Decomp1518 LeanLab.BakerHarmanPintz1997.Audit1617
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

/-- The constant family fails the old predicate, which compared width 2Y with factor Y/y1. -/
theorem not_holds42_constant_one {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 20) :
    ¬ Holds42Old ε (fun _ _ => (1 : ℂ)) :=
  not_holds42Old_of_plateau hε hεsmall ⟨0, fun _ _ _ _ _ => rfl⟩

/-- Vacuity instance of the repaired `Holds42`: the zero family, error constant 0. -/
theorem holds42_zero_instance (ε : ℝ) : Holds42 ε (fun _ _ => (0 : ℂ)) := by
  intro A _
  refine ⟨0, 0, fun x _ q _ _ χ y _ _ => ?_⟩
  simp

/-- The trapezoid meets every hypothesis of the repaired `Lemma11`, so the repaired Lemma has
instances of positive density. -/
theorem repaired_lemma11_hypotheses_instance {ε : ℝ} (hε : 0 ≤ ε) :
    (∀ x k, ‖cP x k‖ ≤ tau k ^ (0 : ℝ)) ∧
    ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (T0 x)..(T1 ε x),
          ‖(⟨cP x, Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half t)‖ ≤
          C * x ^ (1 / 2 : ℝ) / L x ^ A) ∧
        (∫ t in (T0 x)..(T1 ε x),
          ‖(⟨cP x, Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩ : DP).eval χ (half (-t))‖ ≤
          C * x ^ (1 / 2 : ℝ) / L x ^ A) := by
  refine ⟨fun x k => by simpa using cP_norm x k, fun A hA => ?_⟩
  obtain ⟨X1, h1⟩ := plateau_mean hε id (fun _ => rfl) A hA
  obtain ⟨X2, h2⟩ := plateau_mean hε (fun t => -t) (fun t => abs_neg t) A hA
  exact ⟨385, max X1 X2, fun x hx q _ hq χ =>
    ⟨h1 x ((le_max_left _ _).trans hx) q hq χ, h2 x ((le_max_right _ _).trans hx) q hq χ⟩⟩

/-- For large x, 2Y is at most y1, and the power error of the repaired form is below Y/L^A. -/
theorem interval_ev {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 20) {A : ℝ} (hA : 0 < A) :
    ∃ X1 : ℝ, ∀ x, X1 ≤ x → 1 ≤ x ∧ 1 ≤ L x ∧ 2 * Yof ε x ≤ y1 x ∧
      x ^ (0.55 + 11 * ε / 12 : ℝ) ≤ Yof ε x / L x ^ A := by
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, 64 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 64
  have e3 := (isLittleO_log_rpow_rpow_atTop A (by positivity : (0 : ℝ) < ε / 12)).def
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp (e1.and (e2.and e3))
  refine ⟨X1, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hX1 x hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := by linarith
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL _
  refine ⟨h1, by unfold L; linarith, ?_, ?_⟩
  · set y := Real.log x ^ (1 / 3 : ℝ) with hy
    have hy3 : y ^ 3 = Real.log x := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
      norm_num
    have hy4 : 4 ≤ y := by
      by_contra hc
      have hy0 : 0 ≤ y := Real.rpow_nonneg hL.le _
      have : y ^ 3 < 4 ^ 3 := pow_lt_pow_left₀ (not_le.mp hc) hy0 (by norm_num)
      linarith
    have hy3' : 1 + 3 * y ≤ 0.4 * Real.log x := by
      rw [← hy3]
      nlinarith [mul_nonneg (sub_nonneg.mpr hy4) (sub_nonneg.mpr hy4)]
    have e4 : 2 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have e5 : 2 * Real.exp (3 * y) ≤ x ^ (0.4 : ℝ) := by
      rw [Real.rpow_def_of_pos hx0]
      calc 2 * Real.exp (3 * y) ≤ Real.exp 1 * Real.exp (3 * y) :=
            mul_le_mul_of_nonneg_right e4 (Real.exp_pos _).le
        _ = Real.exp (1 + 3 * y) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (Real.log x * 0.4) := Real.exp_le_exp.mpr (by linarith)
    have e6 : Yof ε x ≤ x ^ (0.6 : ℝ) := by
      unfold Yof theta1
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have e7 : x ^ (0.6 : ℝ) * x ^ (0.4 : ℝ) = x := by
      rw [← Real.rpow_add hx0]; norm_num
    have e8 : y1 x * Real.exp (3 * y) = x := by
      rw [y1, mul_assoc, ← Real.exp_add]
      rw [show -3 * Real.log x ^ (1 / 3 : ℝ) + 3 * y = 0 by rw [hy]; ring]
      simp
    have hE : 0 < Real.exp (3 * y) := Real.exp_pos _
    have hY0 : 0 ≤ Yof ε x := Real.rpow_nonneg hx0.le _
    have hP : 0 ≤ x ^ (0.6 : ℝ) := Real.rpow_nonneg hx0.le _
    have : 2 * Yof ε x * Real.exp (3 * y) ≤ y1 x * Real.exp (3 * y) := by
      rw [e8]
      calc 2 * Yof ε x * Real.exp (3 * y) = Yof ε x * (2 * Real.exp (3 * y)) := by ring
        _ ≤ x ^ (0.6 : ℝ) * x ^ (0.4 : ℝ) := mul_le_mul e6 e5 (by positivity) hP
        _ = x := e7
    exact le_of_mul_le_mul_right this hE
  · rw [Real.norm_of_nonneg hLA.le, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul]
      at h3
    unfold L Yof theta1
    rw [le_div_iff₀ hLA]
    calc x ^ (0.55 + 11 * ε / 12 : ℝ) * Real.log x ^ A
        ≤ x ^ (0.55 + 11 * ε / 12 : ℝ) * x ^ (ε / 12) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hx0.le _)
      _ = x ^ (11 / 20 + ε) := by
          rw [← Real.rpow_add hx0]
          congr 1
          norm_num
          ring

/-- Display 4.2 as the proof on page 25 gives it: the sum over I, width 2Y, has factor 2Y/y1.
Taken from the repaired form at y = 2Y. PROVED from `Holds42`. -/
theorem holds42_interval {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 20) {c : ℝ → ℕ → ℂ}
    (h : Holds42 ε c) : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ‖∑ k ∈ Iset ε x, c x k * χ (k : ZMod q) -
        ((2 * Yof ε x / y1 x : ℝ) : ℂ) * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q)‖ ≤
      C * Yof ε x / L x ^ A := by
  intro A hA
  obtain ⟨C, X0, hC⟩ := h A hA
  obtain ⟨X1, hX1⟩ := interval_ev hε hεsmall hA
  refine ⟨3 * |C|, max X0 X1, fun x hx q _ hq χ => ?_⟩
  obtain ⟨h1, hL, hY, hP⟩ := hX1 x ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := by linarith
  have hY1 : 1 ≤ Yof ε x := Real.one_le_rpow h1 (by unfold theta1; linarith)
  have := hC x ((le_max_left _ _).trans hx) q hq χ (2 * Yof ε x) (by linarith) hY
  refine this.trans ?_
  have hLA : 0 < L x ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hq1 : 0 ≤ Yof ε x / L x ^ A := by positivity
  have hP0 : 0 ≤ x ^ (0.55 + 11 * ε / 12 : ℝ) := Real.rpow_nonneg hx0.le _
  have e1 : 2 * Yof ε x / L x ^ A + x ^ (0.55 + 11 * ε / 12 : ℝ) ≤ 3 * (Yof ε x / L x ^ A) := by
    have : 2 * Yof ε x / L x ^ A = 2 * (Yof ε x / L x ^ A) := by ring
    linarith
  calc C * (2 * Yof ε x / L x ^ A + x ^ (0.55 + 11 * ε / 12 : ℝ))
      ≤ |C| * (2 * Yof ε x / L x ^ A + x ^ (0.55 + 11 * ε / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (3 * (Yof ε x / L x ^ A)) := mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    _ = _ := by ring

/-- The two forms together force density zero: a family with both the repaired and the old
property has `(Y/y1) Σ_{I1} c ≪ Y L^{-A}` at every character. So any family of density above
every `L^{-A}` that meets the repaired Lemma cannot meet the old one. PROVED. -/
theorem old_and_repaired_force_small {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 20)
    {c : ℝ → ℕ → ℂ} (h : Holds42 ε c) (hold : Holds42Old ε c) :
    ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ‖((Yof ε x / y1 x : ℝ) : ℂ) * ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q)‖ ≤
      C * Yof ε x / L x ^ A := by
  intro A hA
  obtain ⟨C1, X1, h1⟩ := holds42_interval hε hεsmall h A hA
  obtain ⟨C2, X2, h2⟩ := hold A hA
  refine ⟨C1 + C2, max X1 X2, fun x hx q _ hq χ => ?_⟩
  have a1 := h1 x ((le_max_left _ _).trans hx) q hq χ
  have a2 := h2 x ((le_max_right _ _).trans hx) q hq χ
  set S := ∑ k ∈ Iset ε x, c x k * χ (k : ZMod q)
  set S1 := ∑ k ∈ Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊, c x k * χ (k : ZMod q)
  have hid : ((Yof ε x / y1 x : ℝ) : ℂ) * S1 =
      (S - ((Yof ε x / y1 x : ℝ) : ℂ) * S1) - (S - ((2 * Yof ε x / y1 x : ℝ) : ℂ) * S1) := by
    push_cast
    ring
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  have : (C1 + C2) * Yof ε x / L x ^ A = C2 * Yof ε x / L x ^ A + C1 * Yof ε x / L x ^ A := by
    ring
  rw [this]
  exact add_le_add a2 a1

#print axioms not_holds42_constant_one
#print axioms holds42_zero_instance
#print axioms repaired_lemma11_hypotheses_instance
#print axioms holds42_interval
#print axioms old_and_repaired_force_small
end LeanLab.BakerHarmanPintz1997
