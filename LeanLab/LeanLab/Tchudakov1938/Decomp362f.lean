/- AI-written Lean code by OpenAI Codex, task362, 2026-11-05. Binary Goldbach is open. -/
import LeanLab.PNTPort.DirichletZF.Siegel
import LeanLab.PNTPort.DirichletZF.SiegelLift
namespace LeanLab.Tchudakov1938.Decomp362f
open LeanLab.PNTPort.DirichletZF
/-- P0064, page 30, Lemma 8, nonprincipal real characters. The proved PNTPort estimate extends to all positive moduli by lifting to eight times the modulus. -/
theorem nonprincipal_zero_gap (ε : ℝ) (hε : 0 < ε) : ∃ c : ℝ, 0 < c ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ β : ℝ, β ≤ 1 → DirichletCharacter.LFunction χ β = 0 → c * (N : ℝ) ^ (-ε) ≤ 1 - β := by
  obtain ⟨c, hc, hs⟩ := siegel_zero ε hε
  refine ⟨c * (8 : ℝ)^(-ε), by positivity, fun N _ χ hχ hsq β hβ hz => ?_⟩
  have hdvd : N ∣ 8 * N := Dvd.intro_left 8 rfl
  have : NeZero (8 * N) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne N)⟩
  have h8 : 8 ≤ 8 * N := by have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N); omega
  have hz' : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hdvd χ) (β : ℂ) = 0 := by
    rw [L_lift hdvd hχ, hz, zero_mul]
  have h := hs (8 * N) h8 _ (lift_ne_one hdvd hχ) (lift_sq hdvd hsq) β hβ hz'
  have hN0 : (0 : ℝ) ≤ N := by positivity
  rw [Nat.cast_mul, Real.mul_rpow (by norm_num) hN0] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- P0064, page 30, Lemma 8, uniform modulus form for nonprincipal real characters. -/
theorem zero_gap_upto (ε : ℝ) (hε : 0 < ε) : ∃ c : ℝ, 0 < c ∧
    ∀ Q : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      (N : ℝ) ≤ Q → χ ≠ 1 → χ ^ 2 = 1 → ∀ β : ℝ, β ≤ 1 →
      DirichletCharacter.LFunction χ β = 0 → c * Q ^ (-ε) ≤ 1 - β := by
  obtain ⟨c, hc, hs⟩ := nonprincipal_zero_gap ε hε
  refine ⟨c, hc, fun Q N _ χ hNQ hχ hsq β hβ hz => ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hN hNQ (by linarith)) hc.le).trans (hs N χ hχ hsq β hβ hz)

/-- LEAF. P0064, page 31, display 9. Substitute xi and zeta into the negative exponent. -/
theorem zeta_gap_scale (M x q : ℝ) (hM : 0 < M) (hx : 1 < x) (hq : 0 < q)
    (hqz : q ≤ (Real.log x ^ (M + 6)) ^ (8 / 3 : ℝ)) :
    Real.log x ^ (-(M + 6) / (M + 7)) ≤ q ^ (-(3 / 8 : ℝ) / (M + 7)) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hneg : -(3 / 8 : ℝ) / (M + 7) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
  have h := Real.rpow_le_rpow_of_nonpos hq hqz hneg
  have heq : ((Real.log x ^ (M + 6)) ^ (8 / 3 : ℝ)) ^ (-(3 / 8 : ℝ) / (M + 7)) =
      Real.log x ^ (-(M + 6) / (M + 7)) := by
    rw [← Real.rpow_mul (Real.rpow_nonneg hlog.le _), ← Real.rpow_mul hlog.le]
    congr 1
    field_simp
  rwa [heq] at h

/-- P0064, page 31, display 9. The nonprincipal real-zero branch follows from the proved
Siegel input and the elementary scale identity. No maximum over characters is introduced. -/
theorem zero_gap_at_zeta (M : ℝ) (hM : 0 < M) : ∃ c : ℝ, 0 < c ∧
    ∀ x : ℝ, 1 < x → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      (N : ℝ) ≤ (Real.log x ^ (M + 6)) ^ (8 / 3 : ℝ) → χ ≠ 1 → χ ^ 2 = 1 →
      ∀ β : ℝ, β ≤ 1 → DirichletCharacter.LFunction χ β = 0 →
        c * Real.log x ^ (-(M + 6) / (M + 7)) ≤ 1 - β := by
  have hε : 0 < (3 / 8 : ℝ) / (M + 7) := by positivity
  obtain ⟨c, hc, hs⟩ := nonprincipal_zero_gap ((3 / 8 : ℝ) / (M + 7)) hε
  refine ⟨c, hc, fun x hx N _ χ hN hχ hsq β hβ hz => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hscale := zeta_gap_scale M x N hM hx hN0 hN
  have hs' : c * (N : ℝ)^(-(3 / 8 : ℝ) / (M + 7)) ≤ 1 - β := by
    simpa only [neg_div] using hs N χ hχ hsq β hβ hz
  exact (mul_le_mul_of_nonneg_left hscale hc.le).trans hs' 

end LeanLab.Tchudakov1938.Decomp362f
