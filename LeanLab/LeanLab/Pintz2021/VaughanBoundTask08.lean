import LeanLab.Pintz2021.AdditiveTypeITask08
import LeanLab.PNTPort.Vinogradov.Final

/-!
The Vaughan input for P0054 Lemma 1, author copy page 3, display 1.10.
The additive proof in PNTPort.Vinogradov uses vaughan_identity, geometric
Type I bounds and Cauchy Schwarz for Type II, as in Davenport chapter 25.
This file connects its natural cutoff to the existing real cutoff statement.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.VaughanBoundTask08

open Finset ArithmeticFunction
open LeanLab.Pintz2021.Lemma1U1369
open LeanLab.PNTPort.LargeSieve

/-- The real cutoff sum is the library's natural cutoff sum at floor x. -/
theorem VS_eq_vinogradov (x α : ℝ) :
    VS x α = LeanLab.PNTPort.Vinogradov.S ⌊x⌋₊ α := by
  unfold VS LeanLab.PNTPort.Vinogradov.S
  symm
  apply sum_subset (Icc_subset_Icc (by omega) le_rfl)
  intro n hn hn'
  have hn0 : n = 0 := by simp only [mem_Icc] at hn hn'; omega
  simp [hn0]

/-- The trivial estimate for denominators beyond the cutoff. -/
theorem norm_VS_trivial {x : ℝ} (hx : 0 ≤ x) (α : ℝ) : ‖VS x α‖ ≤ 6 * x := by
  have hpsi : ‖VS x α‖ ≤ Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_sum_Icc]
    unfold VS
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_e, mul_one, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg]
  have h := Chebyshev.psi_le_const_mul_self hx
  obtain ⟨_, h4⟩ := LeanLab.PNTPort.Vinogradov.log4_bounds
  exact hpsi.trans (h.trans (by nlinarith))

/-- Vaughan's bound for the existing real cutoff statement, with C equal to 24300. -/
theorem vaughanThm31_proved : VaughanThm31 := by
  refine ⟨24300, by norm_num, fun x hx α a q hq hcop happ => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hq1 : 1 ≤ q := hq
  have hq0r : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hlx : (1 / 2 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    have h2 := Real.log_two_gt_d9
    linarith
  let B : ℝ → ℝ := fun y =>
    y / Real.sqrt q + y ^ (4 / 5 : ℝ) + Real.sqrt (y * q)
  have hBx : 0 ≤ B x := by dsimp [B]; positivity
  by_cases hqN : q ≤ ⌊x⌋₊
  · have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
    have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have hB : B (⌊x⌋₊ : ℝ) ≤ B x := by
      dsimp [B]
      exact add_le_add
        (add_le_add (div_le_div_of_nonneg_right hNx (Real.sqrt_nonneg _))
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num)))
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hNx hq0r))
    have hlN : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊x⌋₊)) hNx
    have hL : (1 + Real.log (⌊x⌋₊ : ℝ)) ^ 4 ≤ 81 * Real.log x ^ 4 := by
      calc _ ≤ (3 * Real.log x) ^ 4 :=
          pow_le_pow_left₀ (by have := Real.log_natCast_nonneg ⌊x⌋₊; linarith)
            (by linarith) 4
        _ = _ := by ring
    have hnat := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq1
      (Int.isCoprime_iff_gcd_eq_one.mpr hcop) happ hqN
    calc ‖VS x α‖ = ‖LeanLab.PNTPort.Vinogradov.S ⌊x⌋₊ α‖ := by rw [VS_eq_vinogradov]
      _ ≤ 300 * B (⌊x⌋₊ : ℝ) * (1 + Real.log (⌊x⌋₊ : ℝ)) ^ 4 := hnat
      _ ≤ 300 * B x * (81 * Real.log x ^ 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num)) hL
          (by positivity) (by positivity)
      _ = _ := by dsimp [B]; ring
  · have hxq : x ≤ (q : ℝ) := by
      have hf := Nat.lt_floor_add_one x
      have hgap : (⌊x⌋₊ : ℝ) + 1 ≤ q := by
        exact_mod_cast (by omega : ⌊x⌋₊ + 1 ≤ q)
      linarith
    have hs : x ≤ Real.sqrt (x * q) := by
      rw [Real.le_sqrt hx0 (mul_nonneg hx0 hq0r)]
      nlinarith
    have hxB : x ≤ B x := by
      have h1 : 0 ≤ x / Real.sqrt q := by positivity
      have h2 : 0 ≤ x ^ (4 / 5 : ℝ) := Real.rpow_nonneg hx0 _
      dsimp [B]
      linarith
    have hL : (1 / 16 : ℝ) ≤ Real.log x ^ 4 := by
      calc (1 / 16 : ℝ) = (1 / 2 : ℝ) ^ 4 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hlx 4
    have hprod := mul_le_mul hxB hL (by norm_num : (0 : ℝ) ≤ 1 / 16) hBx
    calc ‖VS x α‖ ≤ 6 * x := norm_VS_trivial hx0 α
      _ ≤ _ := by change 6 * x ≤ 24300 * B x * Real.log x ^ 4; nlinarith

/-- P0054 Lemma 1, now without a cited Vaughan hypothesis. -/
theorem lemma1_proved : ∃ A : ℝ, 0 ≤ A ∧ Lemma1_110 A :=
  lemma1_of_vaughan vaughanThm31_proved

/-- The set form of Lemma 1 without a cited Vaughan hypothesis. -/
theorem lemma1On_proved :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ X1 X P : ℝ, 2 ≤ X1 → X1 ≤ X → 3 ≤ X → 1 ≤ P → P ≤ X →
      ∀ mi : Set ℝ, mi ⊆ (majorArcs P (X / P))ᶜ →
        LeanLab.Pintz2021.MinorArcs.Lemma1On A X1 X P mi :=
  lemma1On_of_vaughan vaughanThm31_proved

/-- P0054 display 3.1 with the lab's explicit logarithmic loss. -/
theorem minor31_proved :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ X1 X : ℝ, 2 ≤ X1 → X1 ≤ X → 3 ≤ X → ∀ M : ℕ,
      ∑ m ∈ range M, ‖LeanLab.Pintz2021.MinorArcs.R2
          (LeanLab.Pintz2021.MinorArcs.S X1 X)
          (Set.Icc (-(1 / 2)) (1 / 2) \ majorArcs (X ^ (7 / 25 : ℝ))
            (X / X ^ (7 / 25 : ℝ))) m‖ ^ 2 ≤
        8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / X ^ (7 / 25 : ℝ) :=
  minor31_of_vaughan vaughanThm31_proved

end LeanLab.Pintz2021.VaughanBoundTask08

#print axioms LeanLab.PNTPort.Vinogradov.vinogradov_minor
#print axioms LeanLab.Pintz2021.VaughanBoundTask08.VS_eq_vinogradov
#print axioms LeanLab.Pintz2021.VaughanBoundTask08.norm_VS_trivial
#print axioms LeanLab.Pintz2021.VaughanBoundTask08.vaughanThm31_proved
#print axioms LeanLab.Pintz2021.VaughanBoundTask08.lemma1_proved
#print axioms LeanLab.Pintz2021.VaughanBoundTask08.lemma1On_proved
#print axioms LeanLab.Pintz2021.VaughanBoundTask08.minor31_proved
