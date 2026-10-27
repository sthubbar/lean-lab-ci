/-
P0099, O. Ramaré and Y. Saouter, Short effective intervals containing primes,
J. Number Theory 98 (2003) 10-33. Copy: papers/P0099.pdf. Lemma 1 read from the rendered
page 14; Theorem 4 and Table 1 as in Theorem3Smooth.lean.

Unit U-6732, session 20261020T1914Z-cloud49. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

Contents.
* `theorem2At1e20_of`: Table 1 row 1, Δ = 81 353 847 for every x ≥ 10^20, CONDITIONAL ON
  `Theorem4Fm` with T0 = 3.3 × 10^9, `Lemma1Upper`, the upper half of Lemma 1 for N(T), and
  `MuStar48Bounds`, μ_48/2 ≤ μ*_48(f_48) ≤ μ_48 with μ_48 = 97!/(48! √97).
* `theorem3_of_theorem4`: Theorem 3 CONDITIONAL ON the same three inputs and ChainCert.
* `w48_bounds`: 0.04364 ≤ w(f_48, 0.39890) ≤ 0.04365, PROVED, from the recurrence (22) by an
  exact rational computation checked by `decide +kernel`.

Why `MuStar48Bounds` is an input. Theorem 4 is stated with μ*_m(f) = ||f^(m)||_1/||f||_1 inside
u, while Table 1 is computed with μ_m(f) = ||f^(m)||_2/||f||_1. The upper bound μ* ≤ μ is
Cauchy-Schwarz plus the L2 identity of (20). The hypotheses α2 ≤ u √Y and Y^α4 ≤ u Y need u
from below, so a lower bound on μ* is needed too; the paper does not state one. f_48^(48) is a
multiple of the Legendre polynomial P_48(2t - 1), and a midpoint sum with 200 000 nodes gives
μ*_48/μ_48 ≈ 0.8606, script build/row1_check_cloud49.py; the factor 1/2 is ample.
-/
import Mathlib
import LeanLab.RamareSaouter2003.Theorem3Smooth

namespace LeanLab.RamareSaouter2003.Row1
open Real LeanLab.RamareSaouter2003.Smooth

/-! ### w(f_48, 0.39890) by exact rational arithmetic -/

def aQ : ℚ := 3989 / 10000
def cQ : ℚ := 4 * aQ * (1 - aQ)
/-- The recurrence (22) in ℚ at a = 0.39890. -/
def vQ : ℕ → ℚ
  | 0 => 2 * aQ
  | k + 1 => ((2 * k + 2) * vQ k + (2 * aQ - 1) * cQ ^ (k + 1)) / (2 * k + 3)
def NQ : ℚ := 2 ^ 96 * (Nat.factorial 48 : ℚ) ^ 2 / (Nat.factorial 97 : ℚ)

theorem wQ_lo : (4364 / 100000 : ℚ) ≤ vQ 48 / NQ := by decide +kernel
theorem wQ_hi : vQ 48 / NQ ≤ (4365 / 100000 : ℚ) := by decide +kernel

theorem vQ_eq (k : ℕ) : ((vQ k : ℚ) : ℝ) = v (fm k) (3989 / 10000) := by
  induction k with
  | zero => rw [v_fm_zero]; simp [vQ, aQ]
  | succ k ih =>
    have h := v_recurrence k (3989 / 10000)
    have hpos : (0 : ℝ) < 2 * k + 3 := by positivity
    have e : v (fm (k + 1)) (3989 / 10000) = ((2 * k + 2) * v (fm k) (3989 / 10000) +
        (2 * (3989 / 10000) - 1) * fm (k + 1) (3989 / 10000)) / (2 * k + 3) := by
      rw [eq_div_iff hpos.ne']; linarith
    rw [e, ← ih]
    simp only [vQ, fm, cQ, aQ]
    push_cast
    ring

theorem w48_eq : w 48 (3989 / 10000) = ((vQ 48 / NQ : ℚ) : ℝ) := by
  unfold w
  rw [norm_fm, ← vQ_eq, Rat.cast_div]
  congr 1
  simp only [NQ]
  push_cast
  norm_num

/-- 0.04364 ≤ w(f_48, 0.39890) ≤ 0.04365. PROVED. -/
theorem w48_bounds : (4364 / 100000 : ℝ) ≤ w 48 (3989 / 10000) ∧
    w 48 (3989 / 10000) ≤ 4365 / 100000 := by
  rw [w48_eq]
  constructor
  · have h := (Rat.cast_le (K := ℝ)).mpr wQ_lo
    rwa [show ((4364 / 100000 : ℚ) : ℝ) = 4364 / 100000 by norm_num] at h
  · have h := (Rat.cast_le (K := ℝ)).mpr wQ_hi
    rwa [show ((4365 / 100000 : ℚ) : ℝ) = 4365 / 100000 by norm_num] at h

/-! ### The named inputs -/

/-- μ_48(f_48) = ||f_48^(48)||_2/||f_48||_1 = 97!/(48! √97), from (20). -/
noncomputable def mu48 : ℝ := (Nat.factorial 97 : ℝ) / ((Nat.factorial 48 : ℝ) * √97)

/-- Cited numerical input: μ_48/2 ≤ μ*_48(f_48) ≤ μ_48. The upper half is Cauchy-Schwarz with
the L2 identity of (20); the lower half is numerical, ratio about 0.8606. Not proved here. -/
def MuStar48Bounds : Prop := mu48 / 2 ≤ muStar 48 ∧ muStar 48 ≤ mu48

/-- Lemma 1, p. 14, upper half: for T ≥ 10^3,
N(T) ≤ (T/2π) log(T/2π) - T/2π + 7/8 + 0.67 log(T/2π). Cited from Rosser, Theorem 19. -/
def Lemma1Upper (NT : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 1000 ≤ T → NT T ≤ T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8 +
    0.67 * Real.log (T / (2 * π))

/-! ### Numerical lemmas -/

theorem exp_pow_bounds (n : ℕ) (hn : n ≠ 0) :
    (2.7182818283 : ℝ) ^ n < Real.exp n ∧ Real.exp n < (2.7182818286 : ℝ) ^ n := by
  have hE : Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul]; ring_nf
  rw [hE]
  exact ⟨pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) hn,
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le hn⟩

theorem logT_bounds : 19 ≤ Real.log (1361250000 / (2 * π)) ∧
    Real.log (1361250000 / (2 * π)) ≤ 19.22 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  obtain ⟨e1, e2⟩ := exp_pow_bounds 19 (by norm_num)
  push_cast at e1 e2
  have hxlo : (1361250000 : ℝ) / (2 * 3.141593) ≤ 1361250000 / (2 * π) := by
    gcongr
  have hxhi : (1361250000 : ℝ) / (2 * π) ≤ 1361250000 / (2 * 3.141592) := by
    gcongr
  have hx : (0 : ℝ) < 1361250000 / (2 * π) := by positivity
  constructor
  · rw [Real.le_log_iff_exp_le hx]
    have : (2.7182818286 : ℝ) ^ 19 ≤ 1361250000 / (2 * 3.141593) := by norm_num
    linarith
  · have hE : (0 : ℝ) < Real.exp 19 := Real.exp_pos _
    have hlog : Real.log (1361250000 / (2 * π)) =
        Real.log (1361250000 / (2 * π) / Real.exp 19) + 19 := by
      rw [Real.log_div hx.ne' hE.ne', Real.log_exp]; ring
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx hE)
    have h2 : 1361250000 / (2 * π) / Real.exp 19 ≤
        1361250000 / (2 * 3.141592) / (2.7182818283 : ℝ) ^ 19 := by
      gcongr
    have h3 : (1361250000 : ℝ) / (2 * 3.141592) / (2.7182818283 : ℝ) ^ 19 ≤ 1.22 := by
      norm_num
    linarith

theorem logT0_bounds : 0 ≤ Real.log (3300000000 / (2 * π)) ∧
    Real.log (3300000000 / (2 * π)) ≤ 21 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  obtain ⟨e1, -⟩ := exp_pow_bounds 21 (by norm_num)
  push_cast at e1
  have hx : (0 : ℝ) < 3300000000 / (2 * π) := by positivity
  have hxlo : (3300000000 : ℝ) / (2 * 3.141593) ≤ 3300000000 / (2 * π) := by gcongr
  have hxhi : (3300000000 : ℝ) / (2 * π) ≤ 3300000000 / (2 * 3.141592) := by gcongr
  constructor
  · apply Real.log_nonneg
    have : (1 : ℝ) ≤ 3300000000 / (2 * 3.141593) := by norm_num
    linarith
  · rw [Real.log_le_iff_le_exp hx]
    have : (3300000000 : ℝ) / (2 * 3.141592) ≤ (2.7182818283 : ℝ) ^ 21 := by norm_num
    linarith

theorem invpi_bounds : 1 / (48 * 3.141593) ≤ 1 / (48 * π) ∧ 1 / (48 * π) ≤ 1 / (48 * 3.141592) := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  constructor <;> gcongr

/-- Bounds on s_48(T) at T = 1 361 250 000. -/
theorem smT_bounds :
    ((1 / (48 * 3.141593)) * (19 + 1 / 48) + 1.34 / 1361250000 * (2 * 19 + 1)) * (1 + 1 / 10 ^ 5)
      ≤ sm 48 1361250000 ∧
    sm 48 1361250000 ≤ ((1 / (48 * 3.141592)) * (19.22 + 1 / 48) +
      1.34 / 1361250000 * (2 * 19.22 + 1)) * (1 + 1 / 10 ^ 5) := by
  obtain ⟨L1, L2⟩ := logT_bounds
  obtain ⟨q1, q2⟩ := invpi_bounds
  unfold sm
  push_cast
  set L := Real.log (1361250000 / (2 * π))
  set q := 1 / (48 * π)
  have hq : 0 < q := by positivity
  constructor
  · apply mul_le_mul_of_nonneg_right _ (by norm_num)
    nlinarith [mul_le_mul q1 (show (19 : ℝ) + 1 / 48 ≤ L + 1 / 48 by linarith) (by norm_num) hq.le]
  · apply mul_le_mul_of_nonneg_right _ (by norm_num)
    nlinarith [mul_le_mul q2 (show L + 1 / 48 ≤ 19.22 + 1 / 48 by linarith) (by linarith)
      (by norm_num : (0 : ℝ) ≤ 1 / (48 * 3.141592))]

theorem smT0_bounds : 0 ≤ sm 48 3300000000 ∧
    sm 48 3300000000 ≤ ((1 / (48 * 3.141592)) * (21 + 1 / 48) +
      1.34 / 3300000000 * (2 * 21 + 1)) * (1 + 1 / 10 ^ 5) := by
  obtain ⟨L1, L2⟩ := logT0_bounds
  obtain ⟨q1, q2⟩ := invpi_bounds
  unfold sm
  push_cast
  set L := Real.log (3300000000 / (2 * π))
  set q := 1 / (48 * π)
  have hq : 0 < q := by positivity
  constructor
  · positivity
  · apply mul_le_mul_of_nonneg_right _ (by norm_num)
    nlinarith [mul_le_mul q2 (show L + 1 / 48 ≤ 21 + 1 / 48 by linarith) (by linarith)
      (by norm_num : (0 : ℝ) ≤ 1 / (48 * 3.141592))]

theorem sqrt97_bounds : (9.8488 : ℝ) ≤ √97 ∧ √97 ≤ 9.8489 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [show (9.8489 : ℝ) = √(9.8489 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)

/-! ### u to the power m + 1 -/

/-- The quantity inside the (m+1)-th root in the definition of u, Theorem 4. -/
noncomputable def innerRS (m : ℕ) (α1 α2 α4 a Y T T0 : ℝ) : ℝ :=
  (1 / alpha3inv m α1 α2 α4 a) * muStar m / (m : ℝ) ^ m * T *
    (sm m T / √Y + sm m T0 / 2 * (T / T0) ^ m)

theorem uRS_pow (m : ℕ) (α1 α2 α4 a Y T T0 : ℝ) (h : 0 ≤ innerRS m α1 α2 α4 a Y T T0) :
    uRS m α1 α2 α4 a Y T T0 ^ (m + 1) = (1.0001 / T) ^ (m + 1) * innerRS m α1 α2 α4 a Y T T0 := by
  unfold uRS
  unfold innerRS at h
  rw [mul_pow]
  congr 1
  rw [show (1 : ℝ) / ((m : ℝ) + 1) = (((m + 1 : ℕ)) : ℝ)⁻¹ by push_cast; ring]
  exact Real.rpow_inv_natCast_pow h (by omega)

theorem uRS_nonneg (m : ℕ) (α1 α2 α4 a Y T T0 : ℝ) (hT : 0 < T)
    (h : 0 ≤ innerRS m α1 α2 α4 a Y T T0) : 0 ≤ uRS m α1 α2 α4 a Y T T0 := by
  unfold uRS
  unfold innerRS at h
  exact mul_nonneg (by positivity) (Real.rpow_nonneg h _)

/-! ### Rational constants for row 1 -/

def muhiQ : ℚ := (Nat.factorial 97 : ℚ) / ((Nat.factorial 48 : ℚ) * (98488 / 10000))
def muloQ : ℚ := (Nat.factorial 97 : ℚ) / ((Nat.factorial 48 : ℚ) * (98489 / 10000))
def smhiQ : ℚ := ((1 / (48 * (3141592 / 10 ^ 6))) * (1922 / 100 + 1 / 48) +
  134 / 100 / 1361250000 * (2 * (1922 / 100) + 1)) * (1 + 1 / 10 ^ 5)
def smloQ : ℚ := ((1 / (48 * (3141593 / 10 ^ 6))) * (19 + 1 / 48) +
  134 / 100 / 1361250000 * (2 * 19 + 1)) * (1 + 1 / 10 ^ 5)
def sm0hiQ : ℚ := ((1 / (48 * (3141592 / 10 ^ 6))) * (21 + 1 / 48) +
  134 / 100 / 3300000000 * (2 * 21 + 1)) * (1 + 1 / 10 ^ 5)
def IUQ : ℚ := (1 / (8826 / 10 ^ 6)) * muhiQ / 48 ^ 48 * 1361250000 *
  (smhiQ / 10 ^ 10 + sm0hiQ / 2 * (1361250000 / 3300000000) ^ 48)
def ILQ : ℚ := (1 / (8845 / 10 ^ 6)) * (muloQ / 2) / 48 ^ 48 * 1361250000 * smloQ
def cQ' : ℚ := 10001 / 10000 / 1361250000
def uhiQ : ℚ := 1 / (81353847 * (1 + (1 - 2 * (3989 / 10000)) * 48))

theorem numU : cQ' ^ 49 * IUQ ≤ uhiQ ^ 49 := by decide +kernel
theorem numA2 : (11 : ℚ) ^ 49 ≤ cQ' ^ 49 * ILQ * (10 ^ 10) ^ 48 := by decide +kernel
theorem numY4 : (1 : ℚ) ≤ cQ' ^ 49 * ILQ * (10 ^ 10) ^ 43 := by decide +kernel
theorem numMu : 48 * uhiQ ≤ 1 / 10000 := by decide +kernel
theorem ILQ_pos : 0 < ILQ := by decide +kernel

theorem castR {q r : ℚ} (h : q ≤ r) : (q : ℝ) ≤ r := Rat.cast_le.mpr h

/-! ### Row 1 -/

theorem alpha3_bounds : (8826 / 10 ^ 6 : ℝ) ≤ alpha3inv 48 0.81 11 (22 / 40) (3989 / 10000) ∧
    alpha3inv 48 0.81 11 (22 / 40) (3989 / 10000) ≤ 8845 / 10 ^ 6 := by
  obtain ⟨w1, w2⟩ := w48_bounds
  unfold alpha3inv
  rw [show (2.001 : ℝ) / (22 / 40) = 4002 / 1100 by norm_num]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; norm_num; linarith
  · rw [div_le_iff₀ (by norm_num)]; norm_num; linarith

theorem inner_bounds (Y : ℝ) (hY : (10 : ℝ) ^ 20 ≤ Y) (hμ : MuStar48Bounds) :
    (ILQ : ℝ) / √Y ≤ innerRS 48 0.81 11 (22 / 40) (3989 / 10000) Y 1361250000 3300000000 ∧
    innerRS 48 0.81 11 (22 / 40) (3989 / 10000) Y 1361250000 3300000000 ≤ IUQ := by
  obtain ⟨A1, A2⟩ := alpha3_bounds
  obtain ⟨s1, s2⟩ := smT_bounds
  obtain ⟨s01, s02⟩ := smT0_bounds
  obtain ⟨r1, r2⟩ := sqrt97_bounds
  obtain ⟨μ1, μ2⟩ := hμ
  have hsY : (10 : ℝ) ^ 10 ≤ √Y := by
    rw [Real.le_sqrt (by positivity) (by linarith)]; norm_num at hY ⊢; linarith
  have hs0 : (0 : ℝ) < √Y := by linarith [show (0 : ℝ) < 10 ^ 10 by norm_num]
  have hmuhi : mu48 ≤ muhiQ := by
    rw [show ((muhiQ : ℚ) : ℝ) = (Nat.factorial 97 : ℝ) / ((Nat.factorial 48 : ℝ) * 9.8488) by
      simp only [muhiQ]; push_cast; norm_num]
    unfold mu48; gcongr
  have hmulo : (muloQ : ℝ) ≤ mu48 := by
    rw [show ((muloQ : ℚ) : ℝ) = (Nat.factorial 97 : ℝ) / ((Nat.factorial 48 : ℝ) * 9.8489) by
      simp only [muloQ]; push_cast; norm_num]
    unfold mu48; gcongr
  have esh : ((smhiQ : ℚ) : ℝ) = ((1 / (48 * 3.141592)) * (19.22 + 1 / 48) +
      1.34 / 1361250000 * (2 * 19.22 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [smhiQ]; push_cast; norm_num
  have esl : ((smloQ : ℚ) : ℝ) = ((1 / (48 * 3.141593)) * (19 + 1 / 48) +
      1.34 / 1361250000 * (2 * 19 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [smloQ]; push_cast; norm_num
  have es0 : ((sm0hiQ : ℚ) : ℝ) = ((1 / (48 * 3.141592)) * (21 + 1 / 48) +
      1.34 / 3300000000 * (2 * 21 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [sm0hiQ]; push_cast; norm_num
  rw [← esh] at s2
  rw [← esl] at s1
  rw [← es0] at s02
  have hsl0 : (0 : ℝ) < smloQ := by
    have : (0 : ℚ) < smloQ := by decide +kernel
    exact_mod_cast this
  have hmul0 : (0 : ℝ) < muloQ := by
    have : (0 : ℚ) < muloQ := by decide +kernel
    exact_mod_cast this
  have hA0 : (0 : ℝ) < alpha3inv 48 0.81 11 (22 / 40) (3989 / 10000) := by linarith
  have hμ0 : 0 ≤ muStar 48 := by linarith
  constructor
  · rw [show ((ILQ : ℚ) : ℝ) = (1 / (8845 / 10 ^ 6)) * ((muloQ : ℝ) / 2) / 48 ^ 48 * 1361250000 *
        smloQ by simp only [ILQ]; push_cast; ring]
    unfold innerRS
    push_cast
    have hk : 0 ≤ sm 48 3300000000 / 2 * (1361250000 / 3300000000 : ℝ) ^ 48 := by positivity
    calc (1 / (8845 / 10 ^ 6)) * ((muloQ : ℝ) / 2) / 48 ^ 48 * 1361250000 * smloQ / √Y
        = (1 / (8845 / 10 ^ 6)) * ((muloQ : ℝ) / 2) / 48 ^ 48 * 1361250000 * (smloQ / √Y) := by
          ring
      _ ≤ 1 / alpha3inv 48 0.81 11 (22 / 40) (3989 / 10000) * muStar 48 / 48 ^ 48 * 1361250000 *
          (sm 48 1361250000 / √Y) := by
          gcongr
          all_goals first | linarith | positivity
      _ ≤ _ := by
          gcongr
          all_goals first | linarith | positivity
  · rw [show ((IUQ : ℚ) : ℝ) = (1 / (8826 / 10 ^ 6)) * (muhiQ : ℝ) / 48 ^ 48 * 1361250000 *
        ((smhiQ : ℝ) / 10 ^ 10 + (sm0hiQ : ℝ) / 2 * (1361250000 / 3300000000) ^ 48) by
        simp only [IUQ]; push_cast; ring]
    unfold innerRS
    push_cast
    gcongr
    all_goals (try linarith)
    exact add_nonneg (div_nonneg (by linarith) hs0.le)
      (mul_nonneg (div_nonneg s01 (by norm_num)) (by positivity))

/-- Table 1 row 1: for every x ≥ 10^20 there is a prime in ]x(1 - 1/81 353 847), x].
CONDITIONAL ON Theorem 4 for f_48 with T0 = 3.3 × 10^9, Lemma 1 upper half for N(T), and
`MuStar48Bounds`. -/
theorem theorem2At1e20_of {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000) (hN : Lemma1Upper NT)
    (hμ : MuStar48Bounds) : Smooth.Theorem2At1e20 := by
  intro Y hY
  obtain ⟨I1, I2⟩ := inner_bounds Y hY hμ
  obtain ⟨A1, A2⟩ := alpha3_bounds
  have hsY : (10 : ℝ) ^ 10 ≤ √Y := by
    rw [Real.le_sqrt (by positivity) (by linarith [show (0:ℝ) ≤ 10 ^ 20 by positivity])]
    norm_num at hY ⊢; linarith
  have hs0 : (0 : ℝ) < √Y := by linarith [show (0 : ℝ) < 10 ^ 10 by norm_num]
  have hIL : (0 : ℝ) < ILQ := by exact_mod_cast ILQ_pos
  have hI0 : 0 ≤ innerRS 48 0.81 11 (22 / 40) (3989 / 10000) Y 1361250000 3300000000 := by
    have : 0 < (ILQ : ℝ) / √Y := div_pos hIL hs0
    linarith
  set u := uRS 48 0.81 11 (22 / 40) (3989 / 10000) Y 1361250000 3300000000 with hu
  have hu0 : 0 ≤ u := uRS_nonneg _ _ _ _ _ _ _ _ (by norm_num) hI0
  have hu49 : u ^ 49 = (cQ' : ℝ) ^ 49 *
      innerRS 48 0.81 11 (22 / 40) (3989 / 10000) Y 1361250000 3300000000 := by
    have h0 := uRS_pow 48 0.81 11 (22 / 40) (3989 / 10000) Y 1361250000 3300000000 hI0
    rw [← hu, show (1.0001 : ℝ) / 1361250000 = ((cQ' : ℚ) : ℝ) by
      simp only [cQ']; push_cast; norm_num] at h0
    exact h0
  have hc0 : (0 : ℝ) < cQ' := by
    have : (0 : ℚ) < cQ' := by decide +kernel
    exact_mod_cast this
  -- upper bound on u
  have huhi : u ≤ uhiQ := by
    have hU := castR numU
    push_cast at hU
    have h0 : (0 : ℝ) ≤ uhiQ := by
      have : (0 : ℚ) ≤ uhiQ := by decide +kernel
      exact_mod_cast this
    refine (pow_le_pow_iff_left₀ hu0 h0 (show (49 : ℕ) ≠ 0 by norm_num)).mp ?_
    rw [hu49]
    calc (cQ' : ℝ) ^ 49 * innerRS 48 0.81 11 (22 / 40) (3989 / 10000) Y 1361250000 3300000000
        ≤ (cQ' : ℝ) ^ 49 * IUQ := by gcongr
      _ ≤ _ := hU
  -- the hypotheses of Theorem 4
  have hT1 : 2 * NT 1361250000 ≤ 0.81 * √Y := by
    have h := hN 1361250000 (by norm_num)
    obtain ⟨L1, L2⟩ := logT_bounds
    have p1 := Real.pi_gt_d6
    have hX : (1361250000 : ℝ) / (2 * π) ≤ 1361250000 / (2 * 3.141592) := by gcongr
    have hX0 : (0 : ℝ) ≤ 1361250000 / (2 * π) := by positivity
    have : (1361250000 : ℝ) / (2 * π) * Real.log (1361250000 / (2 * π)) -
        1361250000 / (2 * π) ≤ 1361250000 / (2 * 3.141592) * 18.22 := by
      nlinarith [mul_le_mul hX (show Real.log (1361250000 / (2 * π)) - 1 ≤ 18.22 by linarith)
        (by linarith) (by norm_num : (0 : ℝ) ≤ 1361250000 / (2 * 3.141592))]
    have : (2 : ℝ) * (1361250000 / (2 * 3.141592) * 18.22 + 7 / 8 + 0.67 * 19.22) ≤
        0.81 * 10 ^ 10 := by norm_num
    nlinarith
  have hmu : ((48 : ℕ) : ℝ) * u ≤ 0.0001 := by
    have := castR numMu
    push_cast at this
    push_cast
    nlinarith
  have h2 : (11 : ℝ) ≤ u * √Y := by
    have hA := castR numA2
    push_cast at hA
    refine (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (show (49 : ℕ) ≠ 0 by norm_num)).mp ?_
    rw [mul_pow, hu49]
    have e : ((ILQ : ℝ) / √Y) * √Y ^ 49 = ILQ * √Y ^ 48 := by
      field_simp
    have hp : ((10 : ℝ) ^ 10) ^ 48 ≤ √Y ^ 48 := by gcongr
    calc (11 : ℝ) ^ 49 ≤ (cQ' : ℝ) ^ 49 * ILQ * (10 ^ 10) ^ 48 := hA
      _ ≤ (cQ' : ℝ) ^ 49 * ILQ * √Y ^ 48 := by gcongr
      _ = (cQ' : ℝ) ^ 49 * (((ILQ : ℝ) / √Y) * √Y ^ 49) := by rw [e]; ring
      _ ≤ _ := by
          rw [mul_assoc]
          gcongr
  have hY4 : Y ^ ((22 : ℝ) / 40) ≤ u * Y := by
    have hB := castR numY4
    push_cast at hB
    have hY1 : (1 : ℝ) ≤ Y := by linarith [show (1 : ℝ) ≤ 10 ^ 20 by norm_num]
    have hY0 : (0 : ℝ) ≤ Y := by linarith
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (show (49 : ℕ) ≠ 0 by norm_num)).mp ?_
    have hl : (Y ^ ((22 : ℝ) / 40)) ^ 49 ≤ √Y ^ 54 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]
      calc Y ^ ((22 : ℝ) / 40 * ((49 : ℕ) : ℝ)) ≤ Y ^ ((27 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
        _ = √Y ^ 54 := by
          rw [Real.rpow_natCast, ← Real.sq_sqrt hY0, ← pow_mul, Real.sqrt_sq (Real.sqrt_nonneg _)]
    have hYs : Y = √Y ^ 2 := (Real.sq_sqrt hY0).symm
    have hp : ((10 : ℝ) ^ 10) ^ 43 ≤ √Y ^ 43 := by gcongr
    have hk : (1 : ℝ) ≤ (cQ' : ℝ) ^ 49 * ILQ * √Y ^ 43 :=
      hB.trans (by gcongr)
    calc (Y ^ ((22 : ℝ) / 40)) ^ 49 ≤ √Y ^ 54 := hl
      _ ≤ (cQ' : ℝ) ^ 49 * ILQ * √Y ^ 43 * √Y ^ 54 := by nlinarith [pow_pos hs0 54]
      _ = (cQ' : ℝ) ^ 49 * (((ILQ : ℝ) / √Y) * √Y ^ 98) := by field_simp
      _ ≤ (cQ' : ℝ) ^ 49 * innerRS 48 0.81 11 (22 / 40) (3989 / 10000) Y 1361250000 3300000000 *
            √Y ^ 98 := by rw [mul_assoc]; gcongr
      _ = (u * Y) ^ 49 := by rw [mul_pow, hu49, hYs, Real.sqrt_sq (Real.sqrt_nonneg _)]; ring
  have hΔ : u * (1 + (1 - 2 * (3989 / 10000)) * ((48 : ℕ) : ℝ)) ≤ 1 / 81353847 := by
    have e : ((uhiQ : ℚ) : ℝ) * (1 + (1 - 2 * (3989 / 10000)) * 48) = 1 / 81353847 := by
      simp only [uhiQ]; push_cast; norm_num
    push_cast
    rw [← e]
    gcongr
  have hY2 : (2 * 10 ^ 12 : ℝ) ≤ Y := by linarith [show (2 * 10 ^ 12 : ℝ) ≤ 10 ^ 20 by norm_num]
  exact prime_of_theorem4 h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith) hY2 (by norm_num) hT1 hmu h2 hY4 (by norm_num) hΔ

/-- Theorem 3 CONDITIONAL ON Theorem 4 for f_48, Lemma 1 for N(T), MuStar48Bounds and the
Section 7 chain certificate. -/
theorem theorem3_of_theorem4 {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000)
    (hN : Lemma1Upper NT) (hμ : MuStar48Bounds)
    (hc : ChainCert 10726905041 ((10 : ℝ) ^ 20) 28314000) :
    ∀ x : ℝ, 10726905041 < x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x :=
  theorem3_of_chain (theorem2At1e20_of h4 hN hμ) hc

end LeanLab.RamareSaouter2003.Row1
