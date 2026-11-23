import LeanLab.Zhan1991.SPLIT_display319_high_1122
import LeanLab.Zhan1991.SPLIT_theorem3_p2_1122

/-!
P0068 Zhan 1991, page 269, the zero free part of the high range of (3.19), "by Lemma 5",
PROVED from Lemma 5. It closes the LEAF `highFree_of_lemma5` of SPLIT_display319_high_1122 by a
separate proof, without editing that file. burst-20261122, session S80.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real

/-- Page 269, the window `[T₁, T₁ + H]` with `|T₁| ≤ 2T` lies in `|t| ≤ N`: with `x = N^{1/8}`,
`T ≤ 2x⁶` and `H ≤ 20x³`, and `4x⁶ + 20x³ ≤ x⁸` once `N ≥ 4096`. PROVED. -/

theorem window_le_N269 (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 c2 c3 c7 : ℝ) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (hc7 : 0 ≤ c7) (hc3 : c1 + c2 + c7 ≤ c3) (hN : (4096 : ℝ) ≤ N)
    (hL : 1 ≤ Real.log N) (hA : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A) (hAN : A ≤ N)
    (hq : 1 ≤ q) (hqL : (q : ℝ) ≤ Real.log N ^ c2)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    2 * T269 N A lam q c7 + H269 N A lam ≤ N := by
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  set x := (N : ℝ) ^ (1 / 8 : ℝ) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hN0 _
  have hx8 : x ^ 8 = N := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hP : (N : ℝ) ^ (5 / 8 : ℝ) = x ^ 5 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hx2 : 8 ≤ x ^ 2 := by
    by_contra h; push Not at h
    have : (x ^ 2) ^ 4 < 8 ^ 4 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have : x ^ 8 < 4096 := by nlinarith
    linarith
  have hx5pos : 0 < x ^ 5 := by
    have : 0 < x := by nlinarith
    positivity
  have hLc3 : 1 ≤ L ^ c3 := Real.one_le_rpow hL (by linarith)
  have hA0 : 0 < A := by nlinarith [hP ▸ hA]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsq : Real.sqrt q ≤ L ^ c2 := by
    refine le_trans ?_ hqL
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  obtain ⟨_, hH⟩ := H269_bounds N A lam q c1 hc1 hL hA0 hAN hq hlam
  have hT := T269_bound N A lam q c1 c7 hc1 hL hA0 hAN hq hlam
  -- powers of L
  have hc3' : 0 ≤ c3 := by linarith
  have hA2 : x ^ 10 * L ^ (c1 + c2 + c7) ≤ A ^ 2 := by
    have h1 : L ^ (c1 + c2 + c7) ≤ L ^ c3 := Real.rpow_le_rpow_of_exponent_le hL hc3
    have h2 : x ^ 5 * L ^ (c1 + c2 + c7) ≤ A := by
      rw [← hP]; exact (mul_le_mul_of_nonneg_left h1 (by rw [hP]; exact hx5pos.le)).trans hA
    have h3 : x ^ 5 ≤ x ^ 5 * L ^ (c1 + c2 + c7) :=
      le_mul_of_one_le_right hx5pos.le (Real.one_le_rpow hL (by linarith))
    calc x ^ 10 * L ^ (c1 + c2 + c7) = x ^ 5 * (x ^ 5 * L ^ (c1 + c2 + c7)) := by ring
      _ ≤ A * A := mul_le_mul (h3.trans h2) h2 (by positivity) hA0.le
      _ = A ^ 2 := by ring
  have hTb : T269 N A lam q c7 ≤ 2 * x ^ 6 := by
    have hLsum : L ^ c2 * L ^ c1 * L ^ c7 = L ^ (c1 + c2 + c7) := by
      rw [Real.rpow_add hL0, Real.rpow_add hL0]; ring
    have hpos : 0 < L ^ (c1 + c2 + c7) := Real.rpow_pos_of_pos hL0 _
    calc T269 N A lam q c7 ≤ 2 * Real.sqrt q * ((N : ℝ) ^ 2 * L ^ c1 / A ^ 2) * L ^ c7 := hT
      _ ≤ 2 * L ^ c2 * ((N : ℝ) ^ 2 * L ^ c1 / A ^ 2) * L ^ c7 := by
          gcongr
      _ = 2 * (N : ℝ) ^ 2 * (L ^ c2 * L ^ c1 * L ^ c7) / A ^ 2 := by ring
      _ = 2 * x ^ 16 * L ^ (c1 + c2 + c7) / A ^ 2 := by rw [hLsum, ← hx8]; ring
      _ ≤ 2 * x ^ 16 * L ^ (c1 + c2 + c7) / (x ^ 10 * L ^ (c1 + c2 + c7)) := by
          gcongr
      _ = 2 * x ^ 6 := by
          have : x ^ 10 ≠ 0 := by positivity
          field_simp
  have hHb : H269 N A lam ≤ 20 * x ^ 3 := by
    have h1 : L ^ c1 ≤ L ^ c3 := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have hLc1 : 0 < L ^ c1 := Real.rpow_pos_of_pos hL0 _
    have h2 : x ^ 5 * L ^ c1 ≤ A := by
      rw [← hP]; exact (mul_le_mul_of_nonneg_left h1 (by rw [hP]; exact hx5pos.le)).trans hA
    calc H269 N A lam ≤ 20 * N * L ^ c1 / A := hH
      _ ≤ 20 * N * L ^ c1 / (x ^ 5 * L ^ c1) := by gcongr
      _ = 20 * x ^ 3 := by rw [← hx8]; field_simp
  have hfin : 4 * x ^ 6 + 20 * x ^ 3 ≤ x ^ 8 := by
    have hx3 : 5 ≤ x ^ 3 := by nlinarith
    nlinarith
  linarith

/-- Page 269, "by Lemma 5": Lemma 5 at height `N`, where `q ≤ (log N)^{c₂}`, leaves no zero with
`β ≥ beta5` in the window, so the count is `0`. PROVED from `Lemma5NoExc`. -/
theorem highFree_of_lemma5_proof (h5 : Lemma5NoExc) : ∃ c0 : ℝ, 0 < c0 ∧ HighFreePart c0 := by
  obtain ⟨c0, hc0, h5'⟩ := h5
  refine ⟨c0, hc0, ?_⟩
  intro c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨T₀, hT₀⟩ := h5' c2 hc2
  refine ⟨c1 + c2 + c7 + 1, by linarith, max (max T₀ 4096) (Real.exp 1), ?_⟩
  intro N A α lam a q _ hN hA hAN hcond hq hlam β T1 hβ hT1
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hN4 : (4096 : ℝ) ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNT : T₀ ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hq1 : 1 ≤ q := hcond.2.2.2.1
  have hwin := window_le_N269 N A lam q c1 c2 (c1 + c2 + c7 + 1) c7 hc1.le hc2.le hc7.le
    (by linarith) hN4 hL1 hA hAN hq1 hq hcond.2.2.1
  have hH0 : 0 ≤ H269 N A lam := by
    obtain ⟨h10, _⟩ := H269_bounds N A lam q c1 hc1.le hL1
      (by
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        have : 0 < (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + c7 + 1) :=
          mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _)
        linarith) hAN hq1 hcond.2.2.1
    linarith
  apply zeroCountZ_eq_zero_of_free
  intro χ ρ hρ1 hρ0 hre him1 him2
  have habs : |ρ.im| ≤ N := by
    rw [abs_le]
    have := abs_le.mp hT1
    constructor <;> nlinarith [abs_nonneg T1, le_abs_self T1, neg_abs_le T1]
  have := hT₀ q N hNT hq χ ρ hρ1 hρ0 habs
  unfold beta5 at hβ
  linarith

end LeanLab.Zhan1991
