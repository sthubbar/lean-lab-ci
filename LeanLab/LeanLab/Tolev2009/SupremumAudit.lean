/-
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/
import LeanLab.Tolev2009.L2Bound

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.SupremumAudit

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Displays19to20
open LeanLab.Tolev2009.L2Bound

/-- Dropping all oscillation gives a uniform bound with no negative log saving. -/
theorem coarse_sup (lam : ℕ → ℝ) (l₃ K₃ N : ℕ) (hlam : ∀ k, |lam k| ≤ 1)
    (hl₃ : l₃ ≤ N) (hK₃ : (K₃ : ℝ) ^ 2 ≤ N) (hL : 1 ≤ Real.log N) (α : ℝ) :
    ‖Kfun lam l₃ K₃ N α‖ ≤ Real.sqrt 17 * N * Real.log N ^ (10 : ℕ) := by
  let P := primeSet 1 0 N
  let w : ℕ → ℝ := fun p => Real.log p * weight lam l₃ K₃ p
  have hc : (P.card : ℝ) ≤ N := by
    apply Nat.cast_le.mpr
    have hs : P ⊆ Icc 1 N := by
      intro p hp
      rcases mem_filter.mp hp with ⟨hp, hprime, _⟩
      exact mem_Icc.mpr ⟨hprime.one_lt.le, by simpa only [mem_range, Nat.lt_succ_iff] using hp⟩
    simpa using card_le_card hs
  have hm : ∑ p ∈ P, w p ^ 2 = ∫ β in (0 : ℝ)..1, ‖Kfun lam l₃ K₃ N β‖ ^ 2 := by
    rw [← Kfun_mass_shift 0, ← finite_mass 0 P w]
    congr 1
    funext β
    rw [Kfun_eq]
  have hcs := sum_norm_le_sqrt P (fun p => (w p : ℂ) * ee ((p : ℝ) * α))
  simp only [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hcs
  rw [hm] at hcs
  have hL0 : 0 ≤ Real.log N := by linarith
  have hmass := display12_L2 lam l₃ K₃ N hlam hl₃ hK₃ hL
  calc
    _ ≤ ∑ p ∈ P, ‖(w p : ℂ) * ee ((p : ℝ) * α)‖ := by
      rw [Kfun_eq]
      exact norm_sum_le _ _
    _ ≤ Real.sqrt P.card * Real.sqrt (∫ β in (0 : ℝ)..1, ‖Kfun lam l₃ K₃ N β‖ ^ 2) := by
      simpa only [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs] using hcs
    _ ≤ Real.sqrt N * Real.sqrt (17 * N * Real.log N ^ (20 : ℕ)) :=
      mul_le_mul (Real.sqrt_le_sqrt hc) (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [show Real.log N ^ (20 : ℕ) = (Real.log N ^ (10 : ℕ)) ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
      calc
        _ = Real.sqrt 17 * (Real.sqrt N * Real.sqrt N) * Real.log N ^ (10 : ℕ) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]

/-- The coarse exponent cannot give the required saving by a change of absolute constant. -/
theorem coarse_exponent_gap (A L C : ℝ) (hA : 10 ^ 4 ≤ A) (hL : 1 < L) (hC : C < L) :
    C * L ^ (350 - 4 * A) < Real.sqrt 17 * L ^ (10 : ℕ) := by
  have hL0 : 0 < L := by linarith
  have hs : (1 : ℝ) ≤ Real.sqrt 17 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hp : L * L ^ (350 - 4 * A) ≤ L ^ (10 : ℝ) := by
    calc
      _ = L ^ ((350 - 4 * A) + 1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have hstrict := mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hL0 (350 - 4 * A))
  have hscale : L ^ (10 : ℝ) ≤ Real.sqrt 17 * L ^ (10 : ℕ) := by
    rw [show L ^ (10 : ℝ) = L ^ (10 : ℕ) by norm_cast]
    exact le_mul_of_one_le_left (by positivity) hs
  exact hstrict.trans_le (hp.trans hscale)

/-- The failure of exponent absorption also occurs along actual integer N. -/
theorem coarse_bound_not_absorbable (A C : ℝ) (hA : 10 ^ 4 ≤ A) :
    ∃ N : ℕ, 1 ≤ Real.log N ∧
      C * N * Real.log N ^ (350 - 4 * A) < Real.sqrt 17 * N * Real.log N ^ (10 : ℕ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (max C 0 + 2))
  have hN0 : (0 : ℝ) < N := (Real.exp_pos _).trans hN
  have hlog : max C 0 + 2 < Real.log N := (Real.lt_log_iff_exp_lt hN0).mpr hN
  have hL : 1 < Real.log N := by have := le_max_right C 0; linarith
  have hC : C < Real.log N := by have := le_max_left C 0; linarith
  refine ⟨N, hL.le, ?_⟩
  have h := mul_lt_mul_of_pos_right (coarse_exponent_gap A (Real.log N) C hA hL hC) hN0
  convert h using 1 <;> ring

end LeanLab.Tolev2009.SupremumAudit
