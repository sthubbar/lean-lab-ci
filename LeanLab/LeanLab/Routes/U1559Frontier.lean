/-
AI wrote this Lean code. Claude, PC run 20261026T1604Z-17563, unit U-1559, T2 FRONTIER,
explicit Chen threshold, idea I-0132.

Question: in the lab's corrected BJS Section 9 chain, P0009 arXiv 2207.09452 v6, which input
binds the threshold at the lab's model floor exp exp 31.5665, and what does the best published
replacement for it give?  Answer, MODEL numerics in Routes/numerics/U1559: the Siegel zero term
m(X3), through nu of eqs 81 and 91, binds; it also blocks pbar1 > 59.  Banks, arXiv 2610.15483 v1,
2026-10-11, an unrefereed preprint making the OpenAI manuscript explicit, Theorem 1.1:
(1 - beta) log q >= 3.0e-3 for every real zero beta in (0,1) of L(s, chi), chi primitive real of
conductor q >= 3.  Then nu >= 3e-3 / log K, about 1e6 times the Bordignon plus 4 value at
log K near 47, the Siegel term vanishes, pbar1 = 67, pbar2 = 61 become admissible and the model floor
drops to log log X2 = 28.117 for a positive Chen count, 28.127 at kappa = 2e-4.  There the binding
input is the printed u0 = 1e9 of BJS Theorem 44, through alpha >= about 1e9 / log X2.

This file: the Banks input as a sealed cited Prop, the nu bound from it, the comparison with the
Bordignon form, the Good admissibility test, and the Section 9 combination step at any t >= 28,
so that the target ChenPosAt 28.127 is reduced to the sieve inputs at 28.127.
Chen's theorem is not in doubt. Binary Goldbach is OPEN.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanLab.ChenExplicit.ChenPos

open Real

noncomputable section
namespace LeanLab.Routes.U1559

/-! ## 1. The cited input -/

/-- CITED, Banks arXiv 2610.15483 v1, Theorem 1.1 second assertion, c = 3.0e-3:
for every primitive real Dirichlet character chi of conductor q >= 3, every real zero
beta in (0,1) of L(s, chi) has (1 - beta) log q >= 3.0e-3.  An unrefereed preprint.
`chi ^ 2 = 1` with primitivity at q >= 3 is the lab's reading of "primitive real". -/
def BanksThm11 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ q → χ.IsPrimitive → χ ^ 2 = 1 →
    ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      (3 / 1000 : ℝ) ≤ (1 - β) * Real.log q

/-- The nu bound used in BJS eqs 81 and 91, from Banks: every modulus q <= K gives
1 - beta >= 3e-3 / log K.  CONDITIONAL ON `BanksThm11`. -/
theorem nu_of_banks (hB : BanksThm11) (K : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hqK : (q : ℝ) ≤ K) (hprim : χ.IsPrimitive) (hreal : χ ^ 2 = 1)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hz : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (3 / 1000 : ℝ) / Real.log K ≤ 1 - β := by
  have h := hB q χ hq hprim hreal β hβ0 hβ1 hz
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0 < Real.log q := Real.log_pos (by linarith)
  have hlqK : Real.log q ≤ Real.log K := Real.log_le_log (by linarith) hqK
  have h1 : (3 / 1000 : ℝ) / Real.log K ≤ 3 / 1000 / Real.log q :=
    div_le_div_of_nonneg_left (by norm_num) hlq hlqK
  have h2 : (3 / 1000 : ℝ) / Real.log q ≤ 1 - β := by
    rw [div_le_iff₀ hlq]; linarith
  linarith

/-! ## 2. Comparison with the Bordignon form and the Good test -/

lemma one_le_log_of_ge {K : ℝ} (hK : 3 ≤ K) : 1 ≤ Real.log K := by
  have he := Real.exp_one_lt_d9
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

/-- PROVED: for K >= 1e10 the Banks value 3e-3 / log K beats the lab's plus 4 Siegel value
max(100, 4 log K) / (sqrt K log^2 K) of U-1490. -/
theorem banks_beats_siegel (K : ℝ) (hK : 10 ^ 10 ≤ K) :
    max 100 (4 * Real.log K) / (Real.sqrt K * Real.log K ^ 2) < (3 / 1000 : ℝ) / Real.log K := by
  have hL := one_le_log_of_ge (by linarith : (3 : ℝ) ≤ K)
  have hs : (10 ^ 5 : ℝ) ≤ Real.sqrt K := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  set L := Real.log K
  have hL0 : 0 < L := by linarith
  have hS0 : 0 < Real.sqrt K := by linarith
  rw [div_lt_div_iff₀ (by positivity) hL0]
  have hm : max 100 (4 * L) < 3 / 1000 * Real.sqrt K * L := by
    apply max_lt
    · nlinarith
    · nlinarith
  calc max 100 (4 * L) * L < 3 / 1000 * Real.sqrt K * L * L := by
        exact mul_lt_mul_of_pos_right hm hL0
    _ = 3 / 1000 * (Real.sqrt K * L ^ 2) := by ring

/-- The lab's R1 of the second nu term, 1/(2 R1 10 log lx), BJS eq 81. -/
abbrev R1 : ℝ := 20452 / 10000

/-- PROVED: the Good test nu(x1) log x1 >= 125 of BJSpX2At3215 holds with the Banks nu at every
level d <= 3, once 1e12 <= log x1 = lx and log lx <= 29. -/
theorem good_of_banks (lx d : ℝ) (hlx : 10 ^ 12 ≤ lx) (hd0 : 0 < d) (hd : d ≤ 3)
    (hlog : Real.log lx ≤ 29) :
    125 ≤ min ((3 / 1000) / (d * Real.log lx)) (1 / (2 * R1 * 10 * Real.log lx)) * lx := by
  have hl0 : 0 < Real.log lx := Real.log_pos (by linarith)
  have h1 : (1 / 29000 : ℝ) ≤ (3 / 1000) / (d * Real.log lx) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h2 : (1 / 29000 : ℝ) ≤ 1 / (2 * R1 * 10 * Real.log lx) := by
    rw [le_div_iff₀ (by positivity)]; norm_num [R1]; nlinarith
  have hm : (1 / 29000 : ℝ) ≤ min ((3 / 1000) / (d * Real.log lx)) (1 / (2 * R1 * 10 * Real.log lx)) :=
    le_min h1 h2
  nlinarith

lemma exp_28_ge : (14 * 10 ^ 11 : ℝ) ≤ exp 28 := by
  have := exp_one_gt_d9
  have e : exp 28 = exp 1 ^ 28 := by rw [exp_one_pow]; norm_num
  have h2 : (2.7182818283 : ℝ) ^ 28 ≤ exp 1 ^ 28 := pow_le_pow_left₀ (by norm_num) this.le 28
  have h3 : (14 * 10 ^ 11 : ℝ) ≤ (2.7182818283 : ℝ) ^ 28 := by norm_num
  linarith

/-- Vacuity instance of `good_of_banks`: lx = 1e12, d = 2, where log lx <= 29. -/
theorem good_of_banks_vacuity :
    125 ≤ min ((3 / 1000) / (2 * Real.log (10 ^ 12))) (1 / (2 * R1 * 10 * Real.log (10 ^ 12))) *
      (10 ^ 12 : ℝ) := by
  apply good_of_banks _ _ le_rfl (by norm_num) (by norm_num)
  have h := exp_28_ge
  have : (10 ^ 12 : ℝ) ≤ exp 29 := by
    have := exp_le_exp.mpr (show (28 : ℝ) ≤ 29 by norm_num); linarith
  rw [Real.log_le_iff_le_exp (by norm_num)]; exact this

/-- Vacuity instance of `banks_beats_siegel` at K = 1e10. -/
theorem banks_beats_siegel_vacuity :
    max 100 (4 * Real.log (10 ^ 10)) / (Real.sqrt (10 ^ 10) * Real.log (10 ^ 10) ^ 2) <
      (3 / 1000 : ℝ) / Real.log (10 ^ 10) :=
  banks_beats_siegel _ le_rfl

/-! ## 3. The Section 9 combination step at any t >= 28 -/

open LeanLab.ChenExplicit

lemma big_exp28 (L : ℝ) (hL : exp 28 ≤ L) : 3 * 10 ^ 15 * L ^ 2 ≤ exp (L / 8) := by
  have hL6 := exp_28_ge
  have hL0 : 0 ≤ L / 8 := by linarith
  have h := Real.pow_div_factorial_le_exp (L / 8) hL0 4
  have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at h
  have hL2 : (196 * 10 ^ 22 : ℝ) ≤ L ^ 2 := by nlinarith
  have : 3 * 10 ^ 15 * L ^ 2 ≤ (L / 8) ^ 4 / 24 := by
    have : (L / 8) ^ 4 / 24 = L ^ 2 * L ^ 2 / 98304 := by ring
    rw [this, le_div_iff₀ (by norm_num)]
    nlinarith [sq_nonneg L]
  linarith

/-- PROVED from the lab's Lemma 37 machinery: ChenPos.lean's combination step with the threshold
hypothesis 32.7 <= t relaxed to 28 <= t, proof otherwise as ChenPos32. -/
theorem chenCount_gt_of_sieveBounds28 (t : ℝ) (ht : 28 ≤ t) (κ : ℝ) (cA cQ cB : ℕ → ℝ)
    (hA : Thm44At t cA) (hQ : Thm50At t cQ) (hB : Thm51At t cB) (hm : MarginKAt t κ cA cQ cB) :
    ∀ N : ℕ, Even N → exp (exp t) < N → κ * mainTerm N < chenCount N := by
  intro N hEven hNt
  have hN : exp (exp 28) < (N : ℝ) :=
    lt_of_le_of_lt (exp_le_exp.mpr (exp_le_exp.mpr ht)) hNt
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : exp 28 < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL6 := exp_28_ge
  have hL0 : 0 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hz2 : 2 ≤ zN N := by
    rw [hz]; have := add_one_le_exp (L / 8); linarith
  have hy0 : 0 < yN N := by rw [hy]; exact exp_pos _
  have hy3 : (N : ℝ) ≤ yN N ^ 3 := by
    rw [hy, ← exp_nat_mul, hNe]; apply exp_le_exp.mpr; push_cast; linarith
  have hchen := chen_inequality N (zN N) (yN N) hz2 hy0 hy3
  have h1 := hA N hEven hNt
  have h2 := hQ N hEven hNt
  have h3 := hB N hEven hNt
  have hmN := hm N hEven hNt
  have hU := U_ge N
  have hL2 : 0 < L ^ 2 := by positivity
  have hM0 : 0 < mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  have hE : 2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * mainTerm N := by
    have hbig := big_exp28 L hL.le
    have e1 : 2 * (N : ℝ) / zN N = 2 * exp (7 * L / 8) := by
      rw [hz, hNe, mul_div_assoc, ← exp_sub]; ring_nf
    have e2 : yN N ≤ exp (7 * L / 8) := by rw [hy]; exact exp_le_exp.mpr (by linarith)
    have e3 : exp L = exp (7 * L / 8) * exp (L / 8) := by rw [← exp_add]; ring_nf
    have hM : 1 / 1000 * exp L / L ^ 2 ≤ mainTerm N := by
      simp only [mainTerm]; rw [← hLdef, ← hNe]
      apply div_le_div_of_nonneg_right _ hL2.le
      rw [hNe]; exact mul_le_mul_of_nonneg_right hU (exp_pos _).le
    have h7 := exp_pos (7 * L / 8)
    have : 3 * exp (7 * L / 8) ≤ 1 / 10 ^ 12 * (1 / 1000 * exp L / L ^ 2) := by
      rw [e3, show 1 / 10 ^ 12 * (1 / 1000 * (exp (7 * L / 8) * exp (L / 8)) / L ^ 2) =
        exp (7 * L / 8) * exp (L / 8) / (10 ^ 15 * L ^ 2) by ring, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbig h7.le]
    linarith
  have hfin := mul_le_mul_of_nonneg_right hmN hM0.le
  nlinarith

theorem chenPos_of_sieveBounds28 (t : ℝ) (ht : 28 ≤ t) (κ : ℝ) (hκ : 0 ≤ κ) (cA cQ cB : ℕ → ℝ)
    (hA : Thm44At t cA) (hQ : Thm50At t cQ) (hB : Thm51At t cB) (hm : MarginKAt t κ cA cQ cB) :
    ChenPosAt t := by
  intro N hEven hNt
  have h := chenCount_gt_of_sieveBounds28 t ht κ cA cQ cB hA hQ hB hm N hEven hNt
  have hM0 : 0 ≤ mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  have : (0 : ℝ) < chenCount N := lt_of_le_of_lt (mul_nonneg hκ hM0) h
  exact_mod_cast this

/-! ## 4. The target -/

/-- The model floor of this unit, log log X2 = 28.127, rounded up from 28.12660 at kappa = 2e-4. -/
abbrev tB : ℝ := 28127 / 1000

/-- OPEN input: the three BJS sieve bounds at tB with the Section 9 margin kappa = 1e-5.
In the MODEL these come from the printed BJS Theorems 44, 50, 51 with alpha = alpha_min(tB),
pbar1 = 67, pbar2 = 61 and nu from `BanksThm11`; not yet built in Lean. -/
def SieveInputsAt (t : ℝ) : Prop :=
  ∃ cA cQ cB : ℕ → ℝ, Thm44At t cA ∧ Thm50At t cQ ∧ Thm51At t cB ∧ MarginKAt t (1 / 10 ^ 5) cA cQ cB

/-- SEALED target of U-1559: every even N > exp(exp 28.127) has a Chen representation. -/
def ChenBanksTarget : Prop := ChenPosAt tB

/-- PROVED: the target follows from the sieve inputs at tB.  So `ChenBanksTarget` is
CONDITIONAL ON `SieveInputsAt tB`, which in turn is to rest on `BanksThm11` and the printed
BJS Theorems 44, 50, 51 at the new parameters. -/
theorem chenBanksTarget_of_inputs (h : SieveInputsAt tB) : ChenBanksTarget := by
  obtain ⟨cA, cQ, cB, hA, hQ, hB, hm⟩ := h
  exact chenPos_of_sieveBounds28 tB (by norm_num) (1 / 10 ^ 5) (by norm_num) cA cQ cB hA hQ hB hm

/-- Vacuity of the threshold hypothesis of the t >= 28 step: tB itself. -/
example : (28 : ℝ) ≤ tB := by norm_num

#print axioms nu_of_banks
#print axioms one_le_log_of_ge
#print axioms banks_beats_siegel
#print axioms good_of_banks
#print axioms exp_28_ge
#print axioms good_of_banks_vacuity
#print axioms banks_beats_siegel_vacuity
#print axioms big_exp28
#print axioms chenCount_gt_of_sieveBounds28
#print axioms chenPos_of_sieveBounds28
#print axioms chenBanksTarget_of_inputs

end LeanLab.Routes.U1559
