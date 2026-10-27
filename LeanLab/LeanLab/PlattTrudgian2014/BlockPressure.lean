/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv math/0201299 page 30, the induction after display 43.
The pressure conclusions are CONDITIONAL ON the supplied block certificate.
-/
import LeanLab.PlattTrudgian2014.BlockCertificate
import LeanLab.PlattTrudgian2014.LambdaBounds

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Complex

def MomentEnvelope (t A b : ℝ) : Prop :=
  ∀ L : ℕ, ∀ ρ : ℂ, ‖ρ‖ ≤ 1 → expMoment L t ρ ≤ A * Real.exp (b * L)

theorem expMoment_trivial (L : ℕ) {t : ℝ} (ht : 0 ≤ t) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) :
    expMoment L t ρ ≤ Real.exp (t * L) := by
  have hc : Real.cosh t ≤ Real.exp t := by
    rw [Real.cosh_eq]
    have hh : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    linarith
  calc
    _ ≤ Real.cosh t ^ L := expMoment_le_cosh_pow L ht hρ
    _ ≤ Real.exp t ^ L := pow_le_pow_left₀ (Real.cosh_pos t).le hc L
    _ = Real.exp (t * L) := by rw [mul_comm, Real.exp_nat_mul]

/-- CONDITIONAL ON BlockBound. -/
theorem expMoment_of_block {h : ℕ} (hh : 0 < h) {t F : ℝ} (ht : 0 ≤ t)
    (hb : BlockBound h t F) (L : ℕ) {ρ : ℂ} (hρ : ‖ρ‖ ≤ 1) :
    expMoment L t ρ ≤ Real.exp (t * h) * Real.exp ((Real.log F / h) * L) := by
  have hF1 := BlockBound_one_le hb
  have hF : 0 < F := lt_of_lt_of_le (by norm_num) hF1
  have hlog : 0 ≤ Real.log F := Real.log_nonneg hF1
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hm := expMoment_block_iterate (L % h) h (L / h) t F hb hρ
  have he : L % h + L / h * h = L := by simpa only [Nat.mul_comm] using Nat.mod_add_div L h
  rw [he] at hm
  have hrem : expMoment (L % h) t ρ ≤ Real.exp (t * h) := by
    apply (expMoment_trivial _ ht hρ).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt L hh).le) ht
  have hpow : F ^ (L / h) ≤ Real.exp ((Real.log F / h) * L) := by
    have hp : F ^ (L / h) = Real.exp (((L / h : ℕ) : ℝ) * Real.log F) := by
      rw [Real.exp_nat_mul, Real.exp_log hF]
    rw [hp, Real.exp_le_exp]
    rw [show Real.log F / h * L = ((L : ℝ) * Real.log F) / h by ring, le_div_iff₀ hhr]
    have hq : (((L / h : ℕ) : ℝ) * h) ≤ L := by exact_mod_cast Nat.div_mul_le_self L h
    have hv := mul_le_mul_of_nonneg_left hq hlog
    nlinarith
  calc
    _ ≤ F ^ (L / h) * expMoment (L % h) t ρ := hm
    _ ≤ F ^ (L / h) * Real.exp (t * h) := mul_le_mul_of_nonneg_left hrem (by positivity)
    _ ≤ Real.exp ((Real.log F / h) * L) * Real.exp (t * h) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

/-- CONDITIONAL ON BlockBound. -/
theorem block_moment_envelope {h : ℕ} (hh : 0 < h) {t F : ℝ} (ht : 0 ≤ t)
    (hb : BlockBound h t F) : MomentEnvelope t (Real.exp (t * h)) (Real.log F / h) :=
  fun L ρ hρ => expMoment_of_block hh ht hb L hρ

#print axioms expMoment_trivial
#print axioms expMoment_of_block
#print axioms block_moment_envelope

end LeanLab.PlattTrudgian2014
