/-
AI wrote this Lean code. Claude, PC run 20261031T0803Z-7768, unit U-1589, T2 FRONTIER, idea I-0132.

The port of the 31.567 chain to log log X2 = 28.127 with pbar1 = 67, pbar2 = 61 is NOT possible
inside BJS arXiv 2207.09452 v6, P0009.  BJS fixes 0 < delta < 2 in section 4.1 p23 and again in
Lemma 41 p38, Theorem 44 p42 and Theorem 51 p44.  Lemma 41, eq 121 p38, makes pbar_i the largest
prime p with log^delta x_i >= prod_{2<q<=p} q.  This file PROVES that at t = 28.127 no delta <= 2
admits pbar1 = 67 for x1(X2), eq 75, nor pbar2 = 61 for x2(X3), X3 = X2^(1/8).  The MODEL value
I-0132 used, delta about 2.0134, lies outside the paper's range, and there the eq 139 c2 term
c2(X2) log^(delta-2) N ... has supremum +infinity over N >= X2, Routes/numerics/U1589.
This is a parameter obstruction, no claim of a paper error.  Binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.BJSEpsM

open Real

noncomputable section
namespace LeanLab.ChenExplicit.DeltaObstructionU1589

open LeanLab.ChenExplicit LeanLab.ChenExplicit.BJS

/-- log log X2 = 28.127, the I-0132 model floor. -/
abbrev tB : ℝ := 28127 / 1000
/-- log x1(X2) = log X2 - 5 log log X2, BJS eq 75 p23. -/
abbrev Lx1 : ℝ := exp tB - 5 * tB
/-- log x2(X3) = log X3 - 15 log log X3 with log X3 = log X2 / 8, BJS eq 75 p23. -/
abbrev Lx2 : ℝ := exp tB / 8 - 15 * log (exp tB / 8)

theorem oddPrimorial_67 : oddPrimorial 67 = 3929160775540133527939545 := by
  unfold oddPrimorial; decide

lemma exp28_ge : (14 * 10 ^ 11 : ℝ) ≤ exp 28 := by
  have := exp_one_gt_d9
  have e : exp 28 = exp 1 ^ 28 := by rw [exp_one_pow]; norm_num
  have h2 : (2.7182818283 : ℝ) ^ 28 ≤ exp 1 ^ 28 := pow_le_pow_left₀ (by norm_num) this.le 28
  have h3 : (14 * 10 ^ 11 : ℝ) ≤ (2.7182818283 : ℝ) ^ 28 := by norm_num
  linarith

lemma exptB_ge : (14 * 10 ^ 11 : ℝ) ≤ exp tB :=
  exp28_ge.trans (exp_le_exp.mpr (by norm_num))

/-- exp(2 tB) = exp(56) exp(0.254) <= 2.7182818286^56 / 0.746, at most 2.805e24. -/
lemma exptB_sq_le : exp tB ^ 2 ≤ (2805 * 10 ^ 21 : ℝ) := by
  have e1 : exp tB ^ 2 = exp 1 ^ 56 * exp (0.254) := by
    rw [← exp_nat_mul, exp_one_pow, ← exp_add]; norm_num
  have h1 : exp 1 ^ 56 ≤ (2.7182818286 : ℝ) ^ 56 :=
    pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 56
  have h2 : exp (0.254 : ℝ) ≤ 1 / (1 - 0.254) :=
    Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ 56 * (1 / (1 - 0.254)) ≤ 2805 * 10 ^ 21 := by norm_num
  rw [e1]
  calc exp 1 ^ 56 * exp 0.254 ≤ (2.7182818286 : ℝ) ^ 56 * (1 / (1 - 0.254)) :=
        mul_le_mul h1 h2 (exp_pos _).le (by norm_num)
    _ ≤ _ := h3

lemma Lx1_ge_one : 1 ≤ Lx1 := by have := exptB_ge; unfold Lx1; norm_num at this ⊢; linarith

lemma log8_le : log (exp tB / 8) ≤ tB := by
  rw [log_div (exp_pos _).ne' (by norm_num), log_exp]
  have : 0 ≤ log (8 : ℝ) := log_nonneg (by norm_num)
  linarith

lemma log8_nonneg : 0 ≤ log (exp tB / 8) := by
  apply log_nonneg; have := exptB_ge; rw [le_div_iff₀ (by norm_num)]; linarith

lemma Lx2_ge_one : 1 ≤ Lx2 := by
  have := exptB_ge; have := log8_le; unfold Lx2; norm_num at *; linarith

lemma rpow_le_sq {x δ : ℝ} (hx : 1 ≤ x) (hδ : δ ≤ 2) : x ^ δ ≤ x ^ 2 := by
  have := Real.rpow_le_rpow_of_exponent_le hx hδ
  rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this

/-- PROVED.  For every delta <= 2: log^delta x1(X2) < 3 5 7 ... 67 at log log X2 = 28.127. -/
theorem pow_lt_primorial67 (δ : ℝ) (hδ : δ ≤ 2) : Lx1 ^ δ < (oddPrimorial 67 : ℝ) := by
  have h1 := rpow_le_sq Lx1_ge_one hδ
  have hle : Lx1 ≤ exp tB := by unfold Lx1; norm_num
  have h2 : Lx1 ^ 2 ≤ exp tB ^ 2 := pow_le_pow_left₀ (by linarith [Lx1_ge_one]) hle 2
  have h3 := exptB_sq_le
  rw [oddPrimorial_67]; push_cast
  linarith

/-- PROVED.  For every delta <= 2: log^delta x2(X3) < 3 5 7 ... 61 with X3 = X2^(1/8). -/
theorem pow_lt_primorial61 (δ : ℝ) (hδ : δ ≤ 2) : Lx2 ^ δ < (oddPrimorial 61 : ℝ) := by
  have h1 := rpow_le_sq Lx2_ge_one hδ
  have hle : Lx2 ≤ exp tB / 8 := by have := log8_nonneg; unfold Lx2; linarith
  have h2 : Lx2 ^ 2 ≤ (exp tB / 8) ^ 2 := pow_le_pow_left₀ (by linarith [Lx2_ge_one]) hle 2
  have h3 := exptB_sq_le
  have e : (exp tB / 8) ^ 2 = exp tB ^ 2 / 64 := by ring
  rw [BJSEm.oddPrimorial_61]; push_cast
  linarith

lemma oddPrimorial_mono {p q : ℕ} (h : p ≤ q) : oddPrimorial p ≤ oddPrimorial q := by
  unfold oddPrimorial
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨by omega, hx.2⟩
  · intro x hx _
    simp only [Finset.mem_filter] at hx
    exact hx.2.1.one_lt.le

lemma pbar_lt_of {B : ℝ} (r : ℕ) (hr : 0 < r) (hB : B < (oddPrimorial r : ℝ)) :
    BJSEm.pbar B < r := by
  have hub : ∀ p ∈ {p : ℕ | p.Prime ∧ (oddPrimorial p : ℝ) ≤ B}, p ≤ r - 1 := by
    intro p hp
    by_contra hc
    have hrp : r ≤ p := by omega
    have := oddPrimorial_mono hrp
    have : (oddPrimorial r : ℝ) ≤ oddPrimorial p := by exact_mod_cast this
    linarith [hp.2]
  have h := csSup_le' (s := {p : ℕ | p.Prime ∧ (oddPrimorial p : ℝ) ≤ B}) hub
  unfold BJSEm.pbar; omega

/-- PROVED.  At t = 28.127, for every delta <= 2, the Lemma 41 prime pbar1 is below 67:
pbar1 = 67 is not admissible in BJS's range 0 < delta < 2. -/
theorem pbar1_lt_67 (δ : ℝ) (hδ : δ ≤ 2) : BJSEm.pbar (Lx1 ^ δ) < 67 :=
  pbar_lt_of 67 (by norm_num) (pow_lt_primorial67 δ hδ)

/-- PROVED.  At t = 28.127, for every delta <= 2, the Lemma 41 prime pbar2 is below 61. -/
theorem pbar2_lt_61 (δ : ℝ) (hδ : δ ≤ 2) : BJSEm.pbar (Lx2 ^ δ) < 61 :=
  pbar_lt_of 61 (by norm_num) (pow_lt_primorial61 δ hδ)

/-- Vacuity instance: the hypothesis delta <= 2 holds at delta = 1.99, so both bounds bite. -/
example : BJSEm.pbar (Lx1 ^ (1.99 : ℝ)) < 67 ∧ BJSEm.pbar (Lx2 ^ (1.99 : ℝ)) < 61 :=
  ⟨pbar1_lt_67 _ (by norm_num), pbar2_lt_61 _ (by norm_num)⟩

#print axioms oddPrimorial_67
#print axioms exptB_sq_le
#print axioms pow_lt_primorial67
#print axioms pow_lt_primorial61
#print axioms oddPrimorial_mono
#print axioms pbar_lt_of
#print axioms pbar1_lt_67
#print axioms pbar2_lt_61

end LeanLab.ChenExplicit.DeltaObstructionU1589
