/-
P0099, O. Ramaré and Y. Saouter 2003, Table 1 row 59, m = 55. Copy: papers/P0099.pdf.

Unit U-6732, session 20261020T1914Z-cloud49. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

* `theorem2_row59_of`: for every x ≥ e^59 there is a prime in ]x(1 - 1/209 257 759), x],
  CONDITIONAL ON `Theorem4Fm` with T0 = 3.3 × 10^9, `Lemma1Upper` and `MuStar55Bounds`,
  μ_55/2 ≤ μ*_55(f_55) ≤ μ_55 with μ_55 = 111!/(55! √111); a midpoint sum gives the ratio
  μ*_55/μ_55 ≈ 0.8606.
* `w55_bounds`: 0.24649 ≤ w(f_55, 0.44529) ≤ 0.24650, PROVED by exact rational arithmetic.
Here the T0 term of u dominates, so the lower bound on u comes from it.
-/
import Mathlib
import LeanLab.RamareSaouter2003.Theorem2Row1

namespace LeanLab.RamareSaouter2003.Row59
open Real LeanLab.RamareSaouter2003.Smooth LeanLab.RamareSaouter2003.Row1

def aQ : ℚ := 44529 / 100000
def cQ : ℚ := 4 * aQ * (1 - aQ)
def vQ : ℕ → ℚ
  | 0 => 2 * aQ
  | k + 1 => ((2 * k + 2) * vQ k + (2 * aQ - 1) * cQ ^ (k + 1)) / (2 * k + 3)
def NQ : ℚ := 2 ^ 110 * (Nat.factorial 55 : ℚ) ^ 2 / (Nat.factorial 111 : ℚ)

theorem wQ_lo : (24649 / 100000 : ℚ) ≤ vQ 55 / NQ := by decide +kernel
theorem wQ_hi : vQ 55 / NQ ≤ (24650 / 100000 : ℚ) := by decide +kernel

theorem vQ_eq (k : ℕ) : ((vQ k : ℚ) : ℝ) = v (fm k) (44529 / 100000) := by
  induction k with
  | zero => rw [v_fm_zero]; simp [vQ, aQ]
  | succ k ih =>
    have h := v_recurrence k (44529 / 100000)
    have hpos : (0 : ℝ) < 2 * k + 3 := by positivity
    have e : v (fm (k + 1)) (44529 / 100000) = ((2 * k + 2) * v (fm k) (44529 / 100000) +
        (2 * (44529 / 100000) - 1) * fm (k + 1) (44529 / 100000)) / (2 * k + 3) := by
      rw [eq_div_iff hpos.ne']; linarith
    rw [e, ← ih]
    simp only [vQ, fm, cQ, aQ]
    push_cast
    ring

theorem w55_bounds : (24649 / 100000 : ℝ) ≤ w 55 (44529 / 100000) ∧
    w 55 (44529 / 100000) ≤ 24650 / 100000 := by
  have e : w 55 (44529 / 100000) = ((vQ 55 / NQ : ℚ) : ℝ) := by
    unfold w
    rw [norm_fm, ← vQ_eq, Rat.cast_div]
    congr 1
    simp only [NQ]
    push_cast
    norm_num
  rw [e]
  constructor
  · have h := (Rat.cast_le (K := ℝ)).mpr wQ_lo
    rwa [show ((24649 / 100000 : ℚ) : ℝ) = 24649 / 100000 by norm_num] at h
  · have h := (Rat.cast_le (K := ℝ)).mpr wQ_hi
    rwa [show ((24650 / 100000 : ℚ) : ℝ) = 24650 / 100000 by norm_num] at h

noncomputable def mu55 : ℝ := (Nat.factorial 111 : ℝ) / ((Nat.factorial 55 : ℝ) * √111)

/-- Cited numerical input: μ_55/2 ≤ μ*_55(f_55) ≤ μ_55. Not proved here. -/
def MuStar55Bounds : Prop := mu55 / 2 ≤ muStar 55 ∧ muStar 55 ≤ mu55

/-! ### Logarithms -/

theorem log_two_exp_bounds (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : n ≠ 0) (ylo yhi : ℝ) (hylo : 0 < ylo)
    (h1 : ylo ≤ x / (2 * Real.exp n)) (h2 : x / (2 * Real.exp n) ≤ yhi) :
    0.6931471803 + n + (1 - ylo⁻¹) ≤ Real.log x ∧ Real.log x ≤ 0.6931471808 + n + (yhi - 1) := by
  have hE : 0 < 2 * Real.exp n := by positivity
  have hy : 0 < x / (2 * Real.exp n) := div_pos hx hE
  have hl : Real.log x = Real.log 2 + n + Real.log (x / (2 * Real.exp n)) := by
    rw [Real.log_div hx.ne' hE.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have a1 := Real.one_sub_inv_le_log_of_pos hy
  have a2 := Real.log_le_sub_one_of_pos hy
  have hinv : (x / (2 * Real.exp n))⁻¹ ≤ ylo⁻¹ := inv_anti₀ hylo h1
  constructor <;> linarith

theorem log_exp_bounds (x : ℝ) (hx : 0 < x) (n : ℕ) (ylo yhi : ℝ) (hylo : 0 < ylo)
    (h1 : ylo ≤ x / Real.exp n) (h2 : x / Real.exp n ≤ yhi) :
    n + (1 - ylo⁻¹) ≤ Real.log x ∧ Real.log x ≤ n + (yhi - 1) := by
  have hE : 0 < Real.exp n := by positivity
  have hy : 0 < x / Real.exp n := div_pos hx hE
  have hl : Real.log x = n + Real.log (x / Real.exp n) := by
    rw [Real.log_div hx.ne' hE.ne', Real.log_exp]; ring
  have a1 := Real.one_sub_inv_le_log_of_pos hy
  have a2 := Real.log_le_sub_one_of_pos hy
  have hinv : (x / Real.exp n)⁻¹ ≤ ylo⁻¹ := inv_anti₀ hylo h1
  constructor <;> linarith

theorem logT_bounds : 19.6630 ≤ Real.log (2178000000 / (2 * π)) ∧
    Real.log (2178000000 / (2 * π)) ≤ 19.6645 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  obtain ⟨e1, e2⟩ := exp_pow_bounds 19 (by norm_num)
  have h := log_two_exp_bounds (2178000000 / (2 * π)) (by positivity) 19 (by norm_num)
    ((2178000000 / (2 * 3.141593)) / (2 * 2.7182818286 ^ 19))
    ((2178000000 / (2 * 3.141592)) / (2 * 2.7182818283 ^ 19)) (by norm_num)
    (by push_cast at e1 e2 ⊢; gcongr <;> linarith) (by push_cast at e1 e2 ⊢; gcongr <;> linarith)
  push_cast at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans ?_ h1; norm_num
  · refine h2.trans ?_; norm_num

theorem logT0_bounds : 20.076 ≤ Real.log (3300000000 / (2 * π)) ∧
    Real.log (3300000000 / (2 * π)) ≤ 20.083 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  obtain ⟨e1, e2⟩ := exp_pow_bounds 20 (by norm_num)
  have h := log_exp_bounds (3300000000 / (2 * π)) (by positivity) 20
    ((3300000000 / (2 * 3.141593)) / 2.7182818286 ^ 20)
    ((3300000000 / (2 * 3.141592)) / 2.7182818283 ^ 20) (by norm_num)
    (by push_cast at e1 e2 ⊢; gcongr <;> linarith) (by push_cast at e1 e2 ⊢; gcongr <;> linarith)
  push_cast at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans ?_ h1; norm_num
  · refine h2.trans ?_; norm_num

/-- s_55 bounds from bounds on the logarithm. -/
theorem sm55_bounds (T Llo Lhi : ℝ) (hT : 0 < T) (h0 : 0 ≤ Llo)
    (hL1 : Llo ≤ Real.log (T / (2 * π))) (hL2 : Real.log (T / (2 * π)) ≤ Lhi) :
    ((1 / (55 * 3.141593)) * (Llo + 1 / 55) + 1.34 / T * (2 * Llo + 1)) * (1 + 1 / 10 ^ 5)
      ≤ sm 55 T ∧
    sm 55 T ≤ ((1 / (55 * 3.141592)) * (Lhi + 1 / 55) + 1.34 / T * (2 * Lhi + 1)) *
      (1 + 1 / 10 ^ 5) := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have q1 : 1 / (55 * 3.141593) ≤ 1 / (55 * π) := by gcongr
  have q2 : 1 / (55 * π) ≤ 1 / (55 * 3.141592) := by gcongr
  have hc : 0 ≤ 1.34 / T := by positivity
  unfold sm
  push_cast
  set L := Real.log (T / (2 * π))
  set q := 1 / (55 * π)
  have hq : 0 < q := by positivity
  constructor
  · apply mul_le_mul_of_nonneg_right _ (by norm_num)
    nlinarith [mul_le_mul q1 (show Llo + 1 / 55 ≤ L + 1 / 55 by linarith) (by linarith) hq.le,
      mul_le_mul_of_nonneg_left (show 2 * Llo + 1 ≤ 2 * L + 1 by linarith) hc]
  · apply mul_le_mul_of_nonneg_right _ (by norm_num)
    nlinarith [mul_le_mul q2 (show L + 1 / 55 ≤ Lhi + 1 / 55 by linarith) (by linarith)
      (by norm_num : (0 : ℝ) ≤ 1 / (55 * 3.141592)),
      mul_le_mul_of_nonneg_left (show 2 * L + 1 ≤ 2 * Lhi + 1 by linarith) hc]

theorem sqrt111_bounds : (10.5356 : ℝ) ≤ √111 ∧ √111 ≤ 10.5357 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [show (10.5357 : ℝ) = √(10.5357 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)

def sLoQ : ℚ := (27182818283 / 10 ^ 10) ^ 29 * (16487212 / 10 ^ 7)

theorem sqrt_exp59 (Y : ℝ) (hY : Real.exp 59 ≤ Y) : (sLoQ : ℝ) ≤ √Y := by
  have e1 := Real.exp_one_gt_d9
  have hh : (1.6487212 : ℝ) ≤ Real.exp (1 / 2) := by
    refine (pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le
      (show (2 : ℕ) ≠ 0 by norm_num)).mp ?_
    rw [← Real.exp_nat_mul]; norm_num; linarith
  obtain ⟨f1, -⟩ := exp_pow_bounds 29 (by norm_num)
  push_cast at f1
  have : Real.exp (59 / 2) = Real.exp 29 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have hs : Real.exp (59 / 2) ≤ √Y := by
    rw [Real.exp_half]; exact Real.sqrt_le_sqrt hY
  have : (sLoQ : ℝ) = (2.7182818283 : ℝ) ^ 29 * 1.6487212 := by
    simp only [sLoQ]; push_cast; norm_num
  have hm : (2.7182818283 : ℝ) ^ 29 * 1.6487212 ≤ Real.exp 29 * Real.exp (1 / 2) :=
    mul_le_mul f1.le hh (by norm_num) (Real.exp_pos _).le
  linarith

/-! ### Rational constants -/

def muhiQ : ℚ := (Nat.factorial 111 : ℚ) / ((Nat.factorial 55 : ℚ) * (105356 / 10000))
def muloQ : ℚ := (Nat.factorial 111 : ℚ) / ((Nat.factorial 55 : ℚ) * (105357 / 10000))
def smf (p L T : ℚ) : ℚ := ((1 / (55 * p)) * (L + 1 / 55) + 134 / 100 / T * (2 * L + 1)) *
  (1 + 1 / 10 ^ 5)
def smhiQ : ℚ := smf (3141592 / 10 ^ 6) (196645 / 10 ^ 4) 2178000000
def sm0hiQ : ℚ := smf (3141592 / 10 ^ 6) (20083 / 1000) 3300000000
def sm0loQ : ℚ := smf (3141593 / 10 ^ 6) (20076 / 1000) 3300000000
def IUQ : ℚ := (1 / (9932 / 10 ^ 5)) * muhiQ / 55 ^ 55 * 2178000000 *
  (smhiQ / sLoQ + sm0hiQ / 2 * (2178000000 / 3300000000) ^ 55)
def K0Q : ℚ := (1 / (9936 / 10 ^ 5)) * (muloQ / 2) / 55 ^ 55 * 2178000000 *
  (sm0loQ / 2 * (2178000000 / 3300000000) ^ 55)
def cQ' : ℚ := 10001 / 10000 / 2178000000
def uhiQ : ℚ := 1 / (209257759 * (1 + (1 - 2 * (44529 / 100000)) * 55))

theorem numU : cQ' ^ 56 * IUQ ≤ uhiQ ^ 56 := by decide +kernel
theorem numA2 : (4199 : ℚ) ^ 56 ≤ cQ' ^ 56 * K0Q * sLoQ ^ 56 := by decide +kernel
theorem numY4 : (1 : ℚ) ≤ cQ' ^ 56 * K0Q * sLoQ ^ 42 := by decide +kernel
theorem numMu : 55 * uhiQ ≤ 1 / 10000 := by decide +kernel
theorem numN : 2 * (2178000000 / (2 * (3141592 / 10 ^ 6)) * (196645 / 10 ^ 4 - 1) + 7 / 8 +
    67 / 100 * (196645 / 10 ^ 4)) ≤ (2 / 1000 : ℚ) * sLoQ := by decide +kernel
theorem K0Q_pos : 0 < K0Q := by decide +kernel
theorem sLoQ_big : (2 * 10 ^ 12 : ℚ) ≤ sLoQ ^ 2 := by decide +kernel

theorem alpha3_bounds : (9932 / 10 ^ 5 : ℝ) ≤ alpha3inv 55 0.002 4199 (25 / 40) (44529 / 100000) ∧
    alpha3inv 55 0.002 4199 (25 / 40) (44529 / 100000) ≤ 9936 / 10 ^ 5 := by
  obtain ⟨w1, w2⟩ := w55_bounds
  unfold alpha3inv
  rw [show (2.001 : ℝ) / (25 / 40) = 2001 * 40 / 25000 by norm_num]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; norm_num; linarith
  · rw [div_le_iff₀ (by norm_num)]; norm_num; linarith

theorem inner_bounds (Y : ℝ) (hY : Real.exp 59 ≤ Y) (hμ : MuStar55Bounds) :
    (K0Q : ℝ) ≤ innerRS 55 0.002 4199 (25 / 40) (44529 / 100000) Y 2178000000 3300000000 ∧
    innerRS 55 0.002 4199 (25 / 40) (44529 / 100000) Y 2178000000 3300000000 ≤ IUQ := by
  obtain ⟨A1, A2⟩ := alpha3_bounds
  obtain ⟨L1, L2⟩ := logT_bounds
  obtain ⟨L01, L02⟩ := logT0_bounds
  obtain ⟨s1, s2⟩ := sm55_bounds 2178000000 19.6630 19.6645 (by norm_num) (by norm_num) L1 L2
  obtain ⟨s01, s02⟩ := sm55_bounds 3300000000 20.076 20.083 (by norm_num) (by norm_num) L01 L02
  obtain ⟨r1, r2⟩ := sqrt111_bounds
  obtain ⟨μ1, μ2⟩ := hμ
  have hsY := sqrt_exp59 Y hY
  have hsL : (0 : ℝ) < sLoQ := by
    have : (0 : ℚ) < sLoQ := by decide +kernel
    exact_mod_cast this
  have hs0 : (0 : ℝ) < √Y := by linarith
  have hmuhi : mu55 ≤ muhiQ := by
    rw [show ((muhiQ : ℚ) : ℝ) = (Nat.factorial 111 : ℝ) / ((Nat.factorial 55 : ℝ) * 10.5356) by
      simp only [muhiQ]; push_cast; norm_num]
    unfold mu55; gcongr
  have hmulo : (muloQ : ℝ) ≤ mu55 := by
    rw [show ((muloQ : ℚ) : ℝ) = (Nat.factorial 111 : ℝ) / ((Nat.factorial 55 : ℝ) * 10.5357) by
      simp only [muloQ]; push_cast; norm_num]
    unfold mu55; gcongr
  have esh : ((smhiQ : ℚ) : ℝ) = ((1 / (55 * 3.141592)) * (19.6645 + 1 / 55) +
      1.34 / 2178000000 * (2 * 19.6645 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [smhiQ, smf]; push_cast; norm_num
  have es0 : ((sm0hiQ : ℚ) : ℝ) = ((1 / (55 * 3.141592)) * (20.083 + 1 / 55) +
      1.34 / 3300000000 * (2 * 20.083 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [sm0hiQ, smf]; push_cast; norm_num
  have es0l : ((sm0loQ : ℚ) : ℝ) = ((1 / (55 * 3.141593)) * (20.076 + 1 / 55) +
      1.34 / 3300000000 * (2 * 20.076 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [sm0loQ, smf]; push_cast; norm_num
  rw [← esh] at s2
  rw [← es0] at s02
  rw [← es0l] at s01
  have hs0l : (0 : ℝ) < sm0loQ := by
    have : (0 : ℚ) < sm0loQ := by decide +kernel
    exact_mod_cast this
  have hmul0 : (0 : ℝ) < muloQ := by
    have : (0 : ℚ) < muloQ := by decide +kernel
    exact_mod_cast this
  have hA0 : (0 : ℝ) < alpha3inv 55 0.002 4199 (25 / 40) (44529 / 100000) := by linarith
  have hμ0 : 0 ≤ muStar 55 := by linarith
  have hsmT : 0 ≤ sm 55 2178000000 := by
    have : (0 : ℝ) ≤ ((1 / (55 * 3.141593)) * (19.6630 + 1 / 55) +
      1.34 / 2178000000 * (2 * 19.6630 + 1)) * (1 + 1 / 10 ^ 5) := by norm_num
    linarith
  constructor
  · rw [show ((K0Q : ℚ) : ℝ) = (1 / (9936 / 10 ^ 5)) * ((muloQ : ℝ) / 2) / 55 ^ 55 * 2178000000 *
        (0 + (sm0loQ : ℝ) / 2 * (2178000000 / 3300000000) ^ 55) by
        simp only [K0Q]; push_cast; ring]
    unfold innerRS
    push_cast
    gcongr
    all_goals (try linarith)
    positivity
  · rw [show ((IUQ : ℚ) : ℝ) = (1 / (9932 / 10 ^ 5)) * (muhiQ : ℝ) / 55 ^ 55 * 2178000000 *
        ((smhiQ : ℝ) / sLoQ + (sm0hiQ : ℝ) / 2 * (2178000000 / 3300000000) ^ 55) by
        simp only [IUQ]; push_cast; ring]
    unfold innerRS
    push_cast
    gcongr
    all_goals (try linarith)
    exact add_nonneg (div_nonneg hsmT hs0.le)
      (mul_nonneg (div_nonneg (by linarith) (by norm_num)) (by positivity))

/-- Table 1 row 59: for every x ≥ e^59 there is a prime in ]x(1 - 1/209 257 759), x].
CONDITIONAL ON Theorem 4 for f_55 with T0 = 3.3 × 10^9, Lemma 1 upper half, MuStar55Bounds. -/
theorem theorem2_row59_of {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000) (hN : Lemma1Upper NT)
    (hμ : MuStar55Bounds) : ∀ x : ℝ, Real.exp 59 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 209257759) < p ∧ (p : ℝ) ≤ x := by
  intro Y hY
  obtain ⟨I1, I2⟩ := inner_bounds Y hY hμ
  have hsY := sqrt_exp59 Y hY
  have hsL : (0 : ℝ) < sLoQ := by
    have : (0 : ℚ) < sLoQ := by decide +kernel
    exact_mod_cast this
  have hs0 : (0 : ℝ) < √Y := by linarith
  have hK : (0 : ℝ) < K0Q := by exact_mod_cast K0Q_pos
  have hI0 : 0 ≤ innerRS 55 0.002 4199 (25 / 40) (44529 / 100000) Y 2178000000 3300000000 := by
    linarith
  set u := uRS 55 0.002 4199 (25 / 40) (44529 / 100000) Y 2178000000 3300000000 with hu
  have hu0 : 0 ≤ u := uRS_nonneg _ _ _ _ _ _ _ _ (by norm_num) hI0
  have hu56 : u ^ 56 = (cQ' : ℝ) ^ 56 *
      innerRS 55 0.002 4199 (25 / 40) (44529 / 100000) Y 2178000000 3300000000 := by
    have h0 := uRS_pow 55 0.002 4199 (25 / 40) (44529 / 100000) Y 2178000000 3300000000 hI0
    rw [← hu, show (1.0001 : ℝ) / 2178000000 = ((cQ' : ℚ) : ℝ) by
      simp only [cQ']; push_cast; norm_num] at h0
    exact h0
  have hc0 : (0 : ℝ) < cQ' := by
    have : (0 : ℚ) < cQ' := by decide +kernel
    exact_mod_cast this
  have hY0 : (0 : ℝ) ≤ Y := (Real.exp_pos 59).le.trans hY
  have hYs : Y = √Y ^ 2 := (Real.sq_sqrt hY0).symm
  have huhi : u ≤ uhiQ := by
    have hU := castR numU
    push_cast at hU
    have h0 : (0 : ℝ) ≤ uhiQ := by
      have : (0 : ℚ) ≤ uhiQ := by decide +kernel
      exact_mod_cast this
    refine (pow_le_pow_iff_left₀ hu0 h0 (show (56 : ℕ) ≠ 0 by norm_num)).mp ?_
    rw [hu56]
    calc (cQ' : ℝ) ^ 56 * innerRS 55 0.002 4199 (25 / 40) (44529 / 100000) Y 2178000000 3300000000
        ≤ (cQ' : ℝ) ^ 56 * IUQ := by gcongr
      _ ≤ _ := hU
  have hT1 : 2 * NT 2178000000 ≤ 0.002 * √Y := by
    have h := hN 2178000000 (by norm_num)
    obtain ⟨L1, L2⟩ := logT_bounds
    have p1 := Real.pi_gt_d6
    have hX : (2178000000 : ℝ) / (2 * π) ≤ 2178000000 / (2 * 3.141592) := by gcongr
    have hX0 : (0 : ℝ) ≤ 2178000000 / (2 * π) := by positivity
    have : (2178000000 : ℝ) / (2 * π) * Real.log (2178000000 / (2 * π)) -
        2178000000 / (2 * π) ≤ 2178000000 / (2 * 3.141592) * (19.6645 - 1) := by
      nlinarith [mul_le_mul hX (show Real.log (2178000000 / (2 * π)) - 1 ≤ 19.6645 - 1 by linarith)
        (by linarith) (by norm_num : (0 : ℝ) ≤ 2178000000 / (2 * 3.141592))]
    have hn := castR numN
    push_cast at hn
    nlinarith
  have hmu : ((55 : ℕ) : ℝ) * u ≤ 0.0001 := by
    have := castR numMu
    push_cast at this
    push_cast
    nlinarith
  have h2 : (4199 : ℝ) ≤ u * √Y := by
    have hA := castR numA2
    push_cast at hA
    refine (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (show (56 : ℕ) ≠ 0 by norm_num)).mp ?_
    rw [mul_pow, hu56]
    have hp : (sLoQ : ℝ) ^ 56 ≤ √Y ^ 56 := by gcongr
    calc (4199 : ℝ) ^ 56 ≤ (cQ' : ℝ) ^ 56 * K0Q * sLoQ ^ 56 := hA
      _ ≤ (cQ' : ℝ) ^ 56 * K0Q * √Y ^ 56 := by gcongr
      _ ≤ _ := by gcongr
  have hY4 : Y ^ ((25 : ℝ) / 40) ≤ u * Y := by
    have hB := castR numY4
    push_cast at hB
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (show (56 : ℕ) ≠ 0 by norm_num)).mp ?_
    have hl : (Y ^ ((25 : ℝ) / 40)) ^ 56 = √Y ^ 70 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]
      rw [show (25 : ℝ) / 40 * ((56 : ℕ) : ℝ) = ((35 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        hYs, ← pow_mul, Real.sqrt_sq (Real.sqrt_nonneg _)]
    have hp : (sLoQ : ℝ) ^ 42 ≤ √Y ^ 42 := by gcongr
    have hk : (1 : ℝ) ≤ (cQ' : ℝ) ^ 56 * K0Q * √Y ^ 42 := hB.trans (by gcongr)
    rw [hl]
    calc √Y ^ 70 ≤ (cQ' : ℝ) ^ 56 * K0Q * √Y ^ 42 * √Y ^ 70 := by nlinarith [pow_pos hs0 70]
      _ = (cQ' : ℝ) ^ 56 * K0Q * √Y ^ 112 := by ring
      _ ≤ (cQ' : ℝ) ^ 56 * innerRS 55 0.002 4199 (25 / 40) (44529 / 100000) Y 2178000000
            3300000000 * √Y ^ 112 := by gcongr
      _ = (u * Y) ^ 56 := by
          rw [mul_pow, hu56, hYs, Real.sqrt_sq (Real.sqrt_nonneg _)]; ring
  have hΔ : u * (1 + (1 - 2 * (44529 / 100000)) * ((55 : ℕ) : ℝ)) ≤ 1 / 209257759 := by
    have e : ((uhiQ : ℚ) : ℝ) * (1 + (1 - 2 * (44529 / 100000)) * 55) = 1 / 209257759 := by
      simp only [uhiQ]; push_cast; norm_num
    push_cast
    rw [← e]
    gcongr
  have hY2 : (2 * 10 ^ 12 : ℝ) ≤ Y := by
    have := castR sLoQ_big
    push_cast at this
    have : (sLoQ : ℝ) ^ 2 ≤ √Y ^ 2 := by gcongr
    nlinarith
  obtain ⟨A1, A2⟩ := alpha3_bounds
  exact prime_of_theorem4 h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith) hY2 (by norm_num) hT1 hmu h2 hY4 (by norm_num) hΔ

end LeanLab.RamareSaouter2003.Row59
