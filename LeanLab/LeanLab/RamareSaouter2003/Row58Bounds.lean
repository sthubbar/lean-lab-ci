import LeanLab.RamareSaouter2003.Theorem2Row59

/-!
P0099, Table 1 row 58 on p. 11 and Theorem 4 on pp. 17 to 21.
The proof reuses the lab's row 59 numerical method with row 58 parameters.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Row58Bounds
open Real LeanLab.RamareSaouter2003.Smooth
  LeanLab.RamareSaouter2003.Row1 LeanLab.RamareSaouter2003.Row59

def aQ : ℚ := 44522 / 100000

def cQ : ℚ := 4 * aQ * (1 - aQ)

def vQ : ℕ → ℚ
  | 0 => 2 * aQ
  | k + 1 => ((2 * k + 2) * vQ k + (2 * aQ - 1) * cQ ^ (k + 1)) / (2 * k + 3)

def NQ : ℚ := 2 ^ 110 * (Nat.factorial 55 : ℚ) ^ 2 / (Nat.factorial 111 : ℚ)


theorem wQ_lo : (2458917 / 10000000 : ℚ) ≤ vQ 55 / NQ := by decide +kernel

theorem wQ_hi : vQ 55 / NQ ≤ (2458918 / 10000000 : ℚ) := by decide +kernel


theorem vQ_eq (k : ℕ) : ((vQ k : ℚ) : ℝ) = v (fm k) (44522 / 100000) := by
  induction k with
  | zero => rw [v_fm_zero]; simp [vQ, aQ]
  | succ k ih =>
    have h := v_recurrence k (44522 / 100000)
    have hpos : (0 : ℝ) < 2 * k + 3 := by positivity
    have e : v (fm (k + 1)) (44522 / 100000) = ((2 * k + 2) * v (fm k) (44522 / 100000) +
        (2 * (44522 / 100000) - 1) * fm (k + 1) (44522 / 100000)) / (2 * k + 3) := by
      rw [eq_div_iff hpos.ne']; linarith
    rw [e, ← ih]
    simp only [vQ, fm, cQ, aQ]
    push_cast
    ring


theorem w55_bounds : (2458917 / 10000000 : ℝ) ≤ w 55 (44522 / 100000) ∧
    w 55 (44522 / 100000) ≤ 2458918 / 10000000 := by
  have e : w 55 (44522 / 100000) = ((vQ 55 / NQ : ℚ) : ℝ) := by
    unfold w
    rw [norm_fm, ← vQ_eq, Rat.cast_div]
    congr 1
    simp only [NQ]
    push_cast
    norm_num
  rw [e]
  constructor
  · have h := (Rat.cast_le (K := ℝ)).mpr wQ_lo
    rwa [show ((2458917 / 10000000 : ℚ) : ℝ) = 2458917 / 10000000 by norm_num] at h
  · have h := (Rat.cast_le (K := ℝ)).mpr wQ_hi
    rwa [show ((2458918 / 10000000 : ℚ) : ℝ) = 2458918 / 10000000 by norm_num] at h


theorem logT_bounds : 19.83 ≤ Real.log (2607000000 / (2 * π)) ∧
    Real.log (2607000000 / (2 * π)) ≤ 19.86 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  obtain ⟨e1, e2⟩ := exp_pow_bounds 19 (by norm_num)
  have h := log_two_exp_bounds (2607000000 / (2 * π)) (by positivity) 19 (by norm_num)
    ((2607000000 / (2 * 3.141593)) / (2 * 2.7182818286 ^ 19))
    ((2607000000 / (2 * 3.141592)) / (2 * 2.7182818283 ^ 19)) (by norm_num)
    (by push_cast at e1 e2 ⊢; gcongr <;> linarith) (by push_cast at e1 e2 ⊢; gcongr <;> linarith)
  push_cast at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · refine le_trans ?_ h1; norm_num
  · refine h2.trans ?_; norm_num


def sLoQ : ℚ := (27182818283 / 10 ^ 10) ^ 29


theorem sqrt_exp58 (Y : ℝ) (hY : Real.exp 58 ≤ Y) : (sLoQ : ℝ) ≤ √Y := by
  have he := (exp_pow_bounds 29 (by norm_num)).1.le
  have hs := Real.sqrt_le_sqrt hY
  rw [← Real.exp_half] at hs
  norm_num at hs
  have hh : (sLoQ : ℝ) = (2.7182818283 : ℝ) ^ 29 := by
    simp only [sLoQ]; push_cast; norm_num
  rw [hh]
  exact he.trans hs

def smhiQ : ℚ := smf (3141592 / 10 ^ 6) (1986 / 100) 2607000000

def IUQ : ℚ := (1 / (993090 / 10 ^ 7)) * Row59.muhiQ / 55 ^ 55 * 2607000000 *
  (smhiQ / sLoQ + Row59.sm0hiQ / 2 * (2607000000 / 3300000000) ^ 55)

def K0Q : ℚ := (1 / (993092 / 10 ^ 7)) * (Row59.muloQ / 2) / 55 ^ 55 * 2607000000 *
  (sm0loQ / 2 * (2607000000 / 3300000000) ^ 55)

def cQ' : ℚ := 10001 / 10000 / 2607000000

def uhiQ : ℚ := 1 / (209026205 * (1 + (1 - 2 * (44522 / 100000)) * 55))


theorem numU : cQ' ^ 56 * IUQ ≤ uhiQ ^ 56 := by decide +kernel

theorem numA2 : (2548 : ℚ) ^ 56 ≤ cQ' ^ 56 * K0Q * sLoQ ^ 56 := by decide +kernel

theorem numY4 : (1 : ℚ) ≤ cQ' ^ 56 * K0Q * sLoQ ^ 42 := by decide +kernel

theorem numMu : 55 * uhiQ ≤ 1 / 10000 := by decide +kernel

theorem K0Q_pos : 0 < K0Q := by decide +kernel

theorem sLoQ_big : (2 * 10 ^ 12 : ℚ) ≤ sLoQ ^ 2 := by decide +kernel


theorem alpha3_bounds : (993090 / 10 ^ 7 : ℝ) ≤ alpha3inv 55 0.004 2548 (25 / 40) (44522 / 100000) ∧
    alpha3inv 55 0.004 2548 (25 / 40) (44522 / 100000) ≤ 993092 / 10 ^ 7 := by
  obtain ⟨w1, w2⟩ := w55_bounds
  unfold alpha3inv
  rw [show (2.001 : ℝ) / (25 / 40) = 2001 * 40 / 25000 by norm_num]
  constructor
  · rw [le_div_iff₀ (by norm_num)]; norm_num; linarith
  · rw [div_le_iff₀ (by norm_num)]; norm_num; linarith


theorem inner_bounds (Y : ℝ) (hY : Real.exp 58 ≤ Y) (hμ : MuStar55Bounds) :
    (K0Q : ℝ) ≤ innerRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 ∧
    innerRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 ≤ IUQ := by
  obtain ⟨A1, A2⟩ := alpha3_bounds
  obtain ⟨L1, L2⟩ := logT_bounds
  obtain ⟨L01, L02⟩ := Row59.logT0_bounds
  obtain ⟨s1, s2⟩ := sm55_bounds 2607000000 19.83 19.86 (by norm_num) (by norm_num) L1 L2
  obtain ⟨s01, s02⟩ := sm55_bounds 3300000000 20.076 20.083 (by norm_num) (by norm_num) L01 L02
  obtain ⟨r1, r2⟩ := sqrt111_bounds
  obtain ⟨μ1, μ2⟩ := hμ
  have hsY := sqrt_exp58 Y hY
  have hsL : (0 : ℝ) < sLoQ := by
    have : (0 : ℚ) < sLoQ := by decide +kernel
    exact_mod_cast this
  have hs0 : (0 : ℝ) < √Y := by linarith
  have hmuhi : mu55 ≤ Row59.muhiQ := by
    rw [show ((Row59.muhiQ : ℚ) : ℝ) = (Nat.factorial 111 : ℝ) / ((Nat.factorial 55 : ℝ) * 10.5356) by
      simp only [Row59.muhiQ]; push_cast; norm_num]
    unfold mu55; gcongr
  have hmulo : (Row59.muloQ : ℝ) ≤ mu55 := by
    rw [show ((Row59.muloQ : ℚ) : ℝ) = (Nat.factorial 111 : ℝ) / ((Nat.factorial 55 : ℝ) * 10.5357) by
      simp only [Row59.muloQ]; push_cast; norm_num]
    unfold mu55; gcongr
  have esh : ((smhiQ : ℚ) : ℝ) = ((1 / (55 * 3.141592)) * (19.86 + 1 / 55) +
      1.34 / 2607000000 * (2 * 19.86 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [smhiQ, smf]; push_cast; norm_num
  have es0 : ((Row59.sm0hiQ : ℚ) : ℝ) = ((1 / (55 * 3.141592)) * (20.083 + 1 / 55) +
      1.34 / 3300000000 * (2 * 20.083 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [Row59.sm0hiQ, smf]; push_cast; norm_num
  have es0l : ((sm0loQ : ℚ) : ℝ) = ((1 / (55 * 3.141593)) * (20.076 + 1 / 55) +
      1.34 / 3300000000 * (2 * 20.076 + 1)) * (1 + 1 / 10 ^ 5) := by
    simp only [sm0loQ, smf]; push_cast; norm_num
  rw [← esh] at s2
  rw [← es0] at s02
  rw [← es0l] at s01
  have hs0l : (0 : ℝ) < sm0loQ := by
    have : (0 : ℚ) < sm0loQ := by decide +kernel
    exact_mod_cast this
  have hmul0 : (0 : ℝ) < Row59.muloQ := by
    have : (0 : ℚ) < Row59.muloQ := by decide +kernel
    exact_mod_cast this
  have hA0 : (0 : ℝ) < alpha3inv 55 0.004 2548 (25 / 40) (44522 / 100000) := by linarith
  have hμ0 : 0 ≤ muStar 55 := by linarith
  have hsmT : 0 ≤ sm 55 2607000000 := by
    have : (0 : ℝ) ≤ ((1 / (55 * 3.141593)) * (19.83 + 1 / 55) +
      1.34 / 2607000000 * (2 * 19.83 + 1)) * (1 + 1 / 10 ^ 5) := by norm_num
    linarith
  constructor
  · rw [show ((K0Q : ℚ) : ℝ) = (1 / (993092 / 10 ^ 7)) * ((Row59.muloQ : ℝ) / 2) / 55 ^ 55 * 2607000000 *
        (0 + (sm0loQ : ℝ) / 2 * (2607000000 / 3300000000) ^ 55) by
        simp only [K0Q]; push_cast; ring]
    unfold innerRS
    push_cast
    gcongr
    all_goals (try linarith)
    positivity
  · rw [show ((IUQ : ℚ) : ℝ) = (1 / (993090 / 10 ^ 7)) * (Row59.muhiQ : ℝ) / 55 ^ 55 * 2607000000 *
        ((smhiQ : ℝ) / sLoQ + (Row59.sm0hiQ : ℝ) / 2 * (2607000000 / 3300000000) ^ 55) by
        simp only [IUQ]; push_cast; ring]
    unfold innerRS
    push_cast
    gcongr
    all_goals (try linarith)
    exact add_nonneg (div_nonneg hsmT hs0.le)
      (mul_nonneg (div_nonneg (by linarith) (by norm_num)) (by positivity))



theorem parameters (hμ : MuStar55Bounds) : ∀ Y : ℝ, Real.exp 58 ≤ Y →
    55 * uRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 ≤ 0.0001 ∧
    2548 ≤ uRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 * √Y ∧
    Y ^ ((25 : ℝ) / 40) ≤ uRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 * Y ∧
    uRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 *
      (1 + (1 - 2 * (44522 / 100000)) * 55) ≤ 1 / 209026205 := by
  intro Y hY
  obtain ⟨I1, I2⟩ := inner_bounds Y hY hμ
  have hsY := sqrt_exp58 Y hY
  have hsL : (0 : ℝ) < sLoQ := by
    have : (0 : ℚ) < sLoQ := by decide +kernel
    exact_mod_cast this
  have hs0 : (0 : ℝ) < √Y := by linarith
  have hK : (0 : ℝ) < K0Q := by exact_mod_cast K0Q_pos
  have hI0 : 0 ≤ innerRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 := by
    linarith
  set u := uRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 with hu
  have hu0 : 0 ≤ u := uRS_nonneg _ _ _ _ _ _ _ _ (by norm_num) hI0
  have hu56 : u ^ 56 = (cQ' : ℝ) ^ 56 *
      innerRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 := by
    have h0 := uRS_pow 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000 hI0
    rw [← hu, show (1.0001 : ℝ) / 2607000000 = ((cQ' : ℚ) : ℝ) by
      simp only [cQ']; push_cast; norm_num] at h0
    exact h0
  have hc0 : (0 : ℝ) < cQ' := by
    have : (0 : ℚ) < cQ' := by decide +kernel
    exact_mod_cast this
  have hY0 : (0 : ℝ) ≤ Y := (Real.exp_pos 58).le.trans hY
  have hYs : Y = √Y ^ 2 := (Real.sq_sqrt hY0).symm
  have huhi : u ≤ uhiQ := by
    have hU := castR numU
    push_cast at hU
    have h0 : (0 : ℝ) ≤ uhiQ := by
      have : (0 : ℚ) ≤ uhiQ := by decide +kernel
      exact_mod_cast this
    refine (pow_le_pow_iff_left₀ hu0 h0 (show (56 : ℕ) ≠ 0 by norm_num)).mp ?_
    rw [hu56]
    calc (cQ' : ℝ) ^ 56 * innerRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000 3300000000
        ≤ (cQ' : ℝ) ^ 56 * IUQ := by gcongr
      _ ≤ _ := hU
  have hmu : ((55 : ℕ) : ℝ) * u ≤ 0.0001 := by
    have := castR numMu
    push_cast at this
    push_cast
    nlinarith
  have h2 : (2548 : ℝ) ≤ u * √Y := by
    have hA := castR numA2
    push_cast at hA
    refine (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (show (56 : ℕ) ≠ 0 by norm_num)).mp ?_
    rw [mul_pow, hu56]
    have hp : (sLoQ : ℝ) ^ 56 ≤ √Y ^ 56 := by gcongr
    calc (2548 : ℝ) ^ 56 ≤ (cQ' : ℝ) ^ 56 * K0Q * sLoQ ^ 56 := hA
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
      _ ≤ (cQ' : ℝ) ^ 56 * innerRS 55 0.004 2548 (25 / 40) (44522 / 100000) Y 2607000000
            3300000000 * √Y ^ 112 := by gcongr
      _ = (u * Y) ^ 56 := by
          rw [mul_pow, hu56, hYs, Real.sqrt_sq (Real.sqrt_nonneg _)]; ring
  have hΔ : u * (1 + (1 - 2 * (44522 / 100000)) * ((55 : ℕ) : ℝ)) ≤ 1 / 209026205 := by
    have e : ((uhiQ : ℚ) : ℝ) * (1 + (1 - 2 * (44522 / 100000)) * 55) = 1 / 209026205 := by
      simp only [uhiQ]; push_cast; norm_num
    push_cast
    rw [← e]
    gcongr
  exact ⟨hmu, h2, hY4, hΔ⟩

end LeanLab.RamareSaouter2003.Row58Bounds
