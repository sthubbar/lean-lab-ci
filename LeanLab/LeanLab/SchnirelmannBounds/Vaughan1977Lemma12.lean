/-
P0066 Vaughan 1977, Lemma 11 and the closing lines of Lemma 12, pp. 103 to 105, read on the
page images. Unit U-6851, CLOUD MANUAL-M1, 2026-10-21, track T1.

(5.1) Ψ(x) = Σ_{3≤p₁≤x-3} Σ_{x-p₁<p₂≤2x-p₁} log p₁. (5.3) F(n) = the same sum with p₁ + p₂ = n.
Lemma 11: |Ψ(x) - x²/log x (1 + (3 - 4 log 2)/(2 log x))| < 0.3 x²/log²x for x ≥ 10^52.
(5.5): Ψ(x) < (16CxN(x)/(1.6 + log x))^{11/15} (Σ_n F(n) Π_{p|n, p>2} ((p-1)/(p-2))^{11/4})^{4/15}.
p. 105: Σ_n F(n) Π ... = Σ_d f(d) Σ_{d|n} F(n) < (2C₁ - 1)/log x · x² (1 + 4.2/log x).
"Therefore ... N(x) > x/(16C(2C₁-1)^{4/11}) · (log x - 0.19)^{15/11}(log x + 1.6)/((log x + 4.2)^{4/11}
log²x) and by (2.10) and (2.11) this gives N(x) > x/25.7 as required."

This file PROVES that closing step, `lemma12_of`: Lemma 12 CONDITIONAL ON Lemma 11, (5.5) and the
p. 105 bound, with C ≤ 0.6602 from (2.10) and C₁ ≤ 6.2130 from (2.11). The constant check:
16C(2C₁-1)^{4/11} ≤ 25.62 and the L-factor is at least 0.99823 for log x ≥ 119, so
x/25.666 < N(x); the paper's 25.7 MATCH, numerics/vaughan_lemma12_M1.py.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Twin

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977Lemma12
open LeanLab.SchnirelmannConstant LeanLab.RieselVaughan1983 LeanLab.SchnirelmannBounds.Vaughan1977
  LeanLab.SchnirelmannBounds.Vaughan1977Sec6

/-- (5.1): `Ψ(x) = Σ_{3≤p₁≤x-3} Σ_{x-p₁<p₂≤2x-p₁} log p₁`. -/
noncomputable def Psi (x : ℝ) : ℝ :=
  ∑ p₁ ∈ (Icc 3 ⌊x - 3⌋₊).filter Nat.Prime,
    ∑ p₂ ∈ (Icc 1 ⌊2 * x - p₁⌋₊).filter (fun p : ℕ => p.Prime ∧ x - p₁ < (p : ℝ)), Real.log p₁

/-- Lemma 11, p. 103. -/
def Lemma11 : Prop := ∀ x : ℝ, 10 ^ 52 ≤ x →
  |Psi x - x ^ 2 / Real.log x * (1 + (3 - 4 * Real.log 2) / (2 * Real.log x))| <
    0.3 * x ^ 2 / Real.log x ^ 2

/-- (5.5), with `≤` for the printed `<`, at a given value `G x` of `Σ_n F(n) Π_{p|n,p>2} ((p-1)/(p-2))^{11/4}`. -/
def Eq55 (C : ℝ) (G : ℝ → ℝ) : Prop := ∀ x : ℝ, 10 ^ 52 ≤ x →
  Psi x ≤ (16 * C * x * NN x / (1.6 + Real.log x)) ^ (11 / 15 : ℝ) * G x ^ (4 / 15 : ℝ)

/-- p. 105, the bound for `Σ_d f(d) Σ_{d|n} F(n)`, from (5.6), (5.10), (2.11) and Lemma 11. -/
def Eq510 (C₁ : ℝ) (G : ℝ → ℝ) : Prop := ∀ x : ℝ, 10 ^ 52 ≤ x →
  0 ≤ G x ∧ G x < (2 * C₁ - 1) / Real.log x * x ^ 2 * (1 + 4.2 / Real.log x)

/-- Lemma 11 gives `Ψ(x) > x² (log x - 0.19)/log²x`. -/
theorem psi_lower (h11 : Lemma11) (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    x ^ 2 * (Real.log x - 0.19) / Real.log x ^ 2 < Psi x := by
  have h := h11 x hx
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have e : x ^ 2 / Real.log x * (1 + (3 - 4 * Real.log 2) / (2 * Real.log x)) - 0.3 * x ^ 2 / Real.log x ^ 2
      = x ^ 2 * (Real.log x + (1.2 - 2 * Real.log 2)) / Real.log x ^ 2 := by
    field_simp; ring
  have h1 := (abs_lt.mp h).1
  have h2 : x ^ 2 * (Real.log x - 0.19) / Real.log x ^ 2 ≤
      x ^ 2 * (Real.log x + (1.2 - 2 * Real.log 2)) / Real.log x ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith

/-- `t^a ≥ 1 + a (1 - 1/t)` for `t > 0`, `a ≥ 0`. -/
theorem rpow_ge (t a : ℝ) (ht : 0 < t) (ha : 0 ≤ a) : 1 + a * (1 - 1 / t) ≤ t ^ a := by
  rw [Real.rpow_def_of_pos ht]
  have h1 : 1 - 1 / t ≤ Real.log t := by
    have := Real.one_sub_inv_le_log_of_pos ht
    simpa [one_div] using this
  have h2 := Real.add_one_le_exp (Real.log t * a)
  nlinarith

/-- `16 C (2C₁ - 1)^{4/11} ≤ 25.62` for `C ≤ 0.6602`, `C₁ ≤ 6.2130`. -/
theorem K_le {C C₁ : ℝ} (hC0 : 0 < C) (hC : C ≤ 0.6602) (hC10 : 1 < 2 * C₁ - 1) (hC1 : C₁ ≤ 6.2130) :
    16 * C * (2 * C₁ - 1) ^ (4 / 11 : ℝ) ≤ 25.62 := by
  have hb : (2 * C₁ - 1) ^ (4 / 11 : ℝ) ≤ 11.426 ^ (4 / 11 : ℝ) :=
    rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hc : (11.426 : ℝ) ^ (4 / 11 : ℝ) ≤ 2.425 := by
    have h : (11.426 : ℝ) ^ (4 : ℕ) ≤ 2.425 ^ (11 : ℕ) := by norm_num
    have e1 : (11.426 : ℝ) ^ (4 / 11 : ℝ) = ((11.426 : ℝ) ^ (4 : ℕ)) ^ ((11 : ℕ)⁻¹ : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul (by norm_num)]; norm_num
    have e2 : (2.425 : ℝ) = ((2.425 : ℝ) ^ (11 : ℕ)) ^ ((11 : ℕ)⁻¹ : ℝ) := by
      rw [pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    rw [e1, e2]
    exact rpow_le_rpow (by positivity) h (by positivity)
  have hp : 0 ≤ (2 * C₁ - 1) ^ (4 / 11 : ℝ) := by positivity
  nlinarith

/-- `e^119 < 10^52`. -/
theorem exp119 : Real.exp 119 < 10 ^ 52 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 119 = Real.exp 1 ^ 119 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 119 < 2.7182818286 ^ 119 := by gcongr
    _ < 10 ^ 52 := by norm_num

/-- `N(x) ≥ 0`: `A` is monotone. -/
theorem NN_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ NN x := by
  unfold NN A NCount
  have : #{n ∈ Icc 1 ⌊x⌋₊ | Even n ∧ AtMostPrimes 2 n} ≤ #{n ∈ Icc 1 ⌊2 * x⌋₊ | Even n ∧ AtMostPrimes 2 n} := by
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    apply Finset.Icc_subset_Icc_right
    exact Nat.floor_le_floor (by linarith)
  have : ((#{n ∈ Icc 1 ⌊x⌋₊ | Even n ∧ AtMostPrimes 2 n} : ℕ) : ℝ) ≤
      #{n ∈ Icc 1 ⌊2 * x⌋₊ | Even n ∧ AtMostPrimes 2 n} := by exact_mod_cast this
  linarith

/-- **Lemma 12, CONDITIONAL ON Lemma 11, (5.5) and the p. 105 bound**, with C ≤ 0.6602 and
C₁ ≤ 6.2130: `N(x) > x/25.7` for `x ≥ 10^52`. -/
theorem lemma12_of {C C₁ : ℝ} {G : ℝ → ℝ} (hC0 : 0 < C) (hC : C ≤ 0.6602)
    (hC10 : 1 < 2 * C₁ - 1) (hC1 : C₁ ≤ 6.2130)
    (h11 : Lemma11) (h55 : Eq55 C G) (h510 : Eq510 C₁ G) : Lemma12 := by
  intro x hx
  by_contra hcon
  push Not at hcon
  have hx0 : 0 < x := by linarith
  have hL119 : 119 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; linarith [exp119]
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  obtain ⟨hG0, hG⟩ := h510 x hx
  have hpsi := psi_lower h11 x hx
  have h5 := h55 x hx
  have hN0 := NN_nonneg x hx0.le
  set B := (2 * C₁ - 1) / L * x ^ 2 * (1 + 4.2 / L) with hB
  have hB0 : 0 < B := by positivity
  set Pl := x ^ 2 * (L - 0.19) / L ^ 2 with hPl
  have hm : 0 < L - 0.19 := by linarith
  have hPl0 : 0 < Pl := by positivity
  set P0 := 16 * C * x * (x / 25.7) / (1.6 + L) with hP0
  have hP00 : 0 < P0 := by positivity
  have hP : 0 ≤ 16 * C * x * NN x / (1.6 + L) := by positivity
  have hPP0 : 16 * C * x * NN x / (1.6 + L) ≤ P0 := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hcon (by positivity)
  -- Ψ < P0^{11/15} B^{4/15}
  have h1 : Pl < P0 ^ (11 / 15 : ℝ) * B ^ (4 / 15 : ℝ) := by
    have hA := rpow_le_rpow hP hPP0 (by norm_num : (0 : ℝ) ≤ 11 / 15)
    have hB' : G x ^ (4 / 15 : ℝ) ≤ B ^ (4 / 15 : ℝ) := rpow_le_rpow hG0 hG.le (by norm_num)
    have := mul_le_mul hA hB' (by positivity) (by positivity)
    linarith
  -- raise to 15/11
  have h2 : Pl ^ (15 / 11 : ℝ) < P0 * B ^ (4 / 11 : ℝ) := by
    have := rpow_lt_rpow hPl0.le h1 (by norm_num : (0 : ℝ) < 15 / 11)
    rw [mul_rpow (by positivity) (by positivity), ← rpow_mul hP00.le, ← rpow_mul hB0.le] at this
    have e3 : (11 / 15 : ℝ) * (15 / 11) = 1 := by norm_num
    have e4 : (4 / 15 : ℝ) * (15 / 11) = 4 / 11 := by norm_num
    rwa [e3, e4, rpow_one] at this
  have e1a : Pl ^ (15 / 11 : ℝ) = Pl * Pl ^ (4 / 11 : ℝ) := by
    rw [show (15 / 11 : ℝ) = 1 + 4 / 11 by norm_num, rpow_add hPl0, rpow_one]
  have hBa : 0 < B ^ (4 / 11 : ℝ) := by positivity
  have e1b : Pl ^ (4 / 11 : ℝ) = (Pl / B) ^ (4 / 11 : ℝ) * B ^ (4 / 11 : ℝ) := by
    rw [div_rpow hPl0.le hB0.le, div_mul_cancel₀ _ hBa.ne']
  rw [e1a, e1b, ← mul_assoc] at h2
  have h3 : Pl * (Pl / B) ^ (4 / 11 : ℝ) < P0 := lt_of_mul_lt_mul_right h2 hBa.le
  have hq : Pl / B = ((L - 0.19) / (L + 4.2)) / (2 * C₁ - 1) := by
    rw [hPl, hB]; field_simp
  have hr0 : 0 < (L - 0.19) / (L + 4.2) := by apply div_pos <;> linarith
  rw [hq, div_rpow hr0.le (by linarith)] at h3
  have hge := rpow_ge ((L - 0.19) / (L + 4.2)) (4 / 11) hr0 (by norm_num)
  have hsimp : 1 + 4 / 11 * (1 - 1 / ((L - 0.19) / (L + 4.2))) = (L - 0.19 - 4 / 11 * 4.39) / (L - 0.19) := by
    have : L - 0.19 ≠ 0 := by linarith
    field_simp; ring
  rw [hsimp] at hge
  set K' := (2 * C₁ - 1) ^ (4 / 11 : ℝ)
  have hK'0 : 0 < K' := by positivity
  have hK : 16 * C * K' ≤ 25.62 := K_le hC0 hC hC10 hC1
  have hlow : Pl * ((L - 0.19 - 4 / 11 * 4.39) / (L - 0.19) / K') ≤
      Pl * (((L - 0.19) / (L + 4.2)) ^ (4 / 11 : ℝ) / K') := by
    apply mul_le_mul_of_nonneg_left _ hPl0.le
    exact div_le_div_of_nonneg_right hge hK'0.le
  have h4 := lt_of_le_of_lt hlow h3
  have e2 : Pl * ((L - 0.19 - 4 / 11 * 4.39) / (L - 0.19) / K') =
      x ^ 2 / 25.7 * (25.7 * (L - 0.19 - 4 / 11 * 4.39)) / (L ^ 2 * K') := by
    rw [hPl]; field_simp
  have e3 : P0 = x ^ 2 / 25.7 * (16 * C) / (1.6 + L) := by rw [hP0]; ring
  rw [e2, e3] at h4
  have hden1 : 0 < L ^ 2 * K' := by positivity
  have hden2 : 0 < 1.6 + L := by linarith
  rw [div_lt_div_iff₀ hden1 hden2] at h4
  have hpoly : 16 * C * K' * L ^ 2 ≤ 25.7 * (L - 0.19 - 4 / 11 * 4.39) * (1.6 + L) := by
    have h5 : 16 * C * K' * L ^ 2 ≤ 25.62 * L ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg L)
    have h6 : 25.62 * L ^ 2 ≤ 25.7 * (L - 0.19 - 4 / 11 * 4.39) * (1.6 + L) := by nlinarith
    linarith
  have hx2 : 0 ≤ x ^ 2 / 25.7 := by positivity
  have h7 := mul_le_mul_of_nonneg_left hpoly hx2
  have l1 : x ^ 2 / 25.7 * (25.7 * (L - 0.19 - 4 / 11 * 4.39)) * (1.6 + L) =
      x ^ 2 / 25.7 * (25.7 * (L - 0.19 - 4 / 11 * 4.39) * (1.6 + L)) := by ring
  have l2 : x ^ 2 / 25.7 * (16 * C) * (L ^ 2 * K') = x ^ 2 / 25.7 * (16 * C * K' * L ^ 2) := by ring
  linarith

/-- **The Theorem**, 27 primes, CONDITIONAL ON (2.14), Lemma 8 and (5.5) at the paper's C,
Lemma 11, and the p. 105 bound with a C₁ ≤ 6.2130 as in (2.11). -/
theorem statement27_of_sec5 {C₁ : ℝ} {G : ℝ → ℝ} (hC10 : 1 < 2 * C₁ - 1) (hC1 : C₁ ≤ 6.2130)
    (hRS : RS33) (h8 : Vaughan1977Lemma10.Lemma8 LeanLab.ChenExplicit.twinC) (h11 : Lemma11)
    (h55 : Eq55 LeanLab.ChenExplicit.twinC G) (h510 : Eq510 C₁ G) : Statement27 :=
  Vaughan1977Twin.statement27_of_twin hRS h8
    (lemma12_of (by linarith [LeanLab.ChenExplicit.twinC_bounds.1]) Vaughan1977Twin.C_lt.le
      hC10 hC1 h11 h55 h510)

end LeanLab.SchnirelmannBounds.Vaughan1977Lemma12

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma12.psi_lower
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma12.rpow_ge
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma12.K_le
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma12.exp119
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma12.NN_nonneg
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma12.lemma12_of
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma12.statement27_of_sec5
