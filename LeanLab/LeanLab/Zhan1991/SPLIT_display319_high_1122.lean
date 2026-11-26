import LeanLab.Zhan1991.SPLIT_theorem3_1122

/-!
P0068 Zhan 1991, page 269, the high range `5/6 ≤ β ≤ 1` of display (3.19), split one step
further along the sentence "For 5/6 ≤ β ≤ 1, by (2.4) and Lemma 5 it follows that", and the
window size bounds both ranges use. burst-20261122, session S80.

Above the Lemma 5 threshold `β ≥ 1 - c₀/(log q + (log (N+2))^{4/5})` the count is `0`; below it
(2.4) gives the bound. `display319_high_of_parts` is PROVED from the two parts. The window bounds
`H269_bounds`, `T269_bound` are PROVED.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open Real

/-- Page 269, `|λ| ≤ 1/(qτ)` with `τ = A² N⁻¹ L^{-c₁}` reads `|λ| ≤ N L^{c₁} / (q A²)`. PROVED. -/
theorem lam_bound269 (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 : ℝ) (hL : 1 ≤ Real.log N)
    (hA0 : 0 < A) (hN : (1 : ℝ) ≤ N) (hq : 1 ≤ q)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    |lam| ≤ N * Real.log N ^ c1 / (q * A ^ 2) := by
  have hL0 : 0 < Real.log N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < N := by linarith
  have e : 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1))) = N * Real.log N ^ c1 / (q * A ^ 2) := by
    rw [Real.rpow_neg hL0.le]
    have : 0 < Real.log N ^ c1 := Real.rpow_pos_of_pos hL0 _
    field_simp
  rwa [e] at hlam

/-- Page 269, `H = 10 (N A⁻¹ + |λ| A)` satisfies `10 ≤ H ≪ N A⁻¹ L^{c₁}`. PROVED. -/
theorem H269_bounds (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 : ℝ) (hc1 : 0 ≤ c1)
    (hL : 1 ≤ Real.log N) (hA0 : 0 < A) (hAN : A ≤ N) (hq : 1 ≤ q)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    10 ≤ H269 N A lam ∧ H269 N A lam ≤ 20 * N * Real.log N ^ c1 / A := by
  have hN : (1 : ℝ) ≤ N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hl := lam_bound269 N A lam q c1 hL hA0 hN hq hlam
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP : 1 ≤ Real.log N ^ c1 := Real.one_le_rpow hL hc1
  have hNA : 1 ≤ (N : ℝ) / A := by rw [le_div_iff₀ hA0]; linarith
  have hlA : |lam| * A ≤ N * Real.log N ^ c1 / A := by
    calc |lam| * A ≤ N * Real.log N ^ c1 / (q * A ^ 2) * A :=
          mul_le_mul_of_nonneg_right hl hA0.le
      _ = N * Real.log N ^ c1 / A / q := by field_simp
      _ ≤ N * Real.log N ^ c1 / A := div_le_self (by positivity) hq0
  have hNA2 : (N : ℝ) / A ≤ N * Real.log N ^ c1 / A := by
    rw [mul_div_right_comm]; exact le_mul_of_one_le_right (by positivity) hP
  unfold H269
  constructor
  · nlinarith [abs_nonneg lam, mul_nonneg (abs_nonneg lam) hA0.le]
  · have : 20 * (N : ℝ) * Real.log N ^ c1 / A = 10 * (N * Real.log N ^ c1 / A + N * Real.log N ^ c1 / A) := by ring
    rw [this]; linarith

/-- Page 269, `T = q^{1/2} (N A⁻¹ + |λ| N) L^{c₇} ≤ 2 q^{1/2} N² A⁻² L^{c₁ + c₇}`. PROVED. -/
theorem T269_bound (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 c7 : ℝ) (hc1 : 0 ≤ c1)
    (hL : 1 ≤ Real.log N) (hA0 : 0 < A) (hAN : A ≤ N) (hq : 1 ≤ q)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))) :
    T269 N A lam q c7 ≤
      2 * Real.sqrt q * ((N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2) * Real.log N ^ c7 := by
  have hN : (1 : ℝ) ≤ N := by
    by_contra h; push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hl := lam_bound269 N A lam q c1 hL hA0 hN hq hlam
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP : 1 ≤ Real.log N ^ c1 := Real.one_le_rpow hL hc1
  have hL0 : 0 ≤ Real.log N := by linarith
  set R := (N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2
  have h1 : (N : ℝ) / A ≤ R := by
    have : (N : ℝ) / A = N * A / A ^ 2 := by field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc (N : ℝ) * A ≤ N * N := mul_le_mul_of_nonneg_left hAN (by linarith)
      _ = N ^ 2 * 1 := by ring
      _ ≤ N ^ 2 * Real.log N ^ c1 := mul_le_mul_of_nonneg_left hP (by positivity)
  have h2 : |lam| * N ≤ R := by
    calc |lam| * N ≤ N * Real.log N ^ c1 / (q * A ^ 2) * N :=
          mul_le_mul_of_nonneg_right hl (by linarith)
      _ = R / q := by simp only [R]; field_simp
      _ ≤ R := div_le_self (by positivity) hq0
  unfold T269
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hc : 0 ≤ Real.log N ^ c7 := Real.rpow_nonneg hL0 _
  calc Real.sqrt q * ((N : ℝ) / A + |lam| * N) * Real.log N ^ c7
      ≤ Real.sqrt q * (R + R) * Real.log N ^ c7 := by gcongr
    _ = _ := by ring

/-- The Lemma 5 threshold at height `N`: `1 - c₀ / (log q + (log (N + 2))^{4/5})`. -/
def beta5 (c0 : ℝ) (N q : ℕ) : ℝ :=
  1 - c0 / (Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ))

/-- Page 269, the zero free part of the high range: with the `c₀` of Lemma 5, no zero is counted
for `β ≥ beta5`. -/
def HighFreePart (c0 : ℝ) : Prop :=
  ∀ c1 c2 B c7 : ℝ, 0 < c1 → 0 < c2 → 0 < B → 0 < c7 → ∃ c3 : ℝ, 0 < c3 ∧ ∃ N₀ : ℝ,
    ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) [NeZero q], N₀ ≤ N →
      (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A → A ≤ N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam →
      (q : ℝ) ≤ Real.log N ^ c2 →
      Real.log N ^ (B + 1) / A ≤ |lam| →
      ∀ β T1 : ℝ, beta5 c0 N q ≤ β → |T1| ≤ 2 * T269 N A lam q c7 →
        zeroCountZ β T1 (H269 N A lam) q = 0

/-- Page 269, the density part of the high range: for `5/6 ≤ β < beta5`,
`N^{β-1} N(β, T₁, H, q) ≪ (q^{12/5} H^{12/5} N⁻¹)^{1-β} L^{c₀} ≪ exp(-c₀ L^{1/5}) ≪ L^{-B-1}`. -/
def HighDensityPart (c0 : ℝ) : Prop :=
  ∀ c1 c2 B c7 : ℝ, 0 < c1 → 0 < c2 → 0 < B → 0 < c7 → ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) [NeZero q], N₀ ≤ N →
      (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A → A ≤ N →
      Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam →
      (q : ℝ) ≤ Real.log N ^ c2 →
      Real.log N ^ (B + 1) / A ≤ |lam| →
      ∀ β T1 : ℝ, 5 / 6 ≤ β → β < beta5 c0 N q → |T1| ≤ 2 * T269 N A lam q c7 →
        (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q ≤ K * Real.log N ^ (-B - 1)

/-- `4096^{5/8} ≥ 40`, so `N ≥ 4096` gives `N^{5/8} ≥ 40`. -/
private theorem forty_le_rpow_five_eighths (N : ℝ) (hN : 4096 ≤ N) :
    (40 : ℝ) ≤ N ^ (5 / 8 : ℝ) := by
  have hval : (40 : ℝ) ≤ (4096 : ℝ) ^ (5 / 8 : ℝ) := by
    have h4096 : (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) := by norm_num
    rw [h4096, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : ((12 : ℕ) : ℝ) * (5 / 8) = 15 / 2 := by norm_num
    rw [h2]
    have hstep : (2 : ℝ) ^ (7 : ℝ) ≤ (2 : ℝ) ^ (15 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h128 : (2 : ℝ) ^ (7 : ℝ) = 128 := by norm_num
    linarith
  exact hval.trans (Real.rpow_le_rpow (by norm_num) hN (by norm_num))

/-- `4096^{1/4} = 8`, so `N ≥ 4096` gives `N^{1/4} ≥ 8`. -/
private theorem eight_le_rpow_quarter (N : ℝ) (hN : 4096 ≤ N) :
    (8 : ℝ) ≤ N ^ (1 / 4 : ℝ) := by
  have hval : (8 : ℝ) ≤ (4096 : ℝ) ^ (1 / 4 : ℝ) := by
    have h4096 : (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) := by norm_num
    rw [h4096, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : ((12 : ℕ) : ℝ) * (1 / 4) = 3 := by norm_num
    rw [h2]
    norm_num
  exact hval.trans (Real.rpow_le_rpow (by norm_num) hN (by norm_num))

/-- For `N ≥ 4096`, `20 N^{3/8} ≤ N/2`. -/
private theorem twenty_rpow_le (N : ℝ) (hN : 4096 ≤ N) :
    20 * N ^ (3 / 8 : ℝ) ≤ N / 2 := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hx : (0 : ℝ) ≤ N ^ (3 / 8 : ℝ) := Real.rpow_nonneg hN0 _
  have h5 := forty_le_rpow_five_eighths N hN
  have hmul : N ^ (5 / 8 : ℝ) * N ^ (3 / 8 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]
    have : (5 / 8 : ℝ) + 3 / 8 = 1 := by norm_num
    rw [this, Real.rpow_one]
  have h40 : 40 * N ^ (3 / 8 : ℝ) ≤ N := by
    calc 40 * N ^ (3 / 8 : ℝ) ≤ N ^ (5 / 8 : ℝ) * N ^ (3 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_right h5 hx
      _ = N := hmul
  linarith

/-- For `N ≥ 4096`, `4 N^{3/4} ≤ N/2`. -/
private theorem four_rpow_le (N : ℝ) (hN : 4096 ≤ N) :
    4 * N ^ (3 / 4 : ℝ) ≤ N / 2 := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hx : (0 : ℝ) ≤ N ^ (3 / 4 : ℝ) := Real.rpow_nonneg hN0 _
  have h8 := eight_le_rpow_quarter N hN
  have hmul : N ^ (1 / 4 : ℝ) * N ^ (3 / 4 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]
    have : (1 / 4 : ℝ) + 3 / 4 = 1 := by norm_num
    rw [this, Real.rpow_one]
  have h8' : 8 * N ^ (3 / 4 : ℝ) ≤ N := by
    calc 8 * N ^ (3 / 4 : ℝ) ≤ N ^ (1 / 4 : ℝ) * N ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right h8 hx
      _ = N := hmul
  linarith

/-- `beta5 c₀ N q < 1` for `c₀ > 0`. -/
private theorem beta5_lt_one (c0 : ℝ) (hc0 : 0 < c0) (N q : ℕ) [NeZero q] :
    beta5 c0 N q < 1 := by
  unfold beta5
  have hq1 : (1 : ℝ) ≤ q := by
    have h : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.out (n := q))
    exact_mod_cast h
  have hq0 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hN2 : (1 : ℝ) < (N : ℝ) + 2 := by
    have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hN2' : (0 : ℝ) < Real.log ((N : ℝ) + 2) := Real.log_pos hN2
  have hr : (0 : ℝ) < Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hN2' _
  have hden : (0 : ℝ) < Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) := by linarith
  have := div_pos hc0 hden
  linarith

/-- `L^a * L^b = L^{a+b}` for `L > 0`. -/
private theorem rpow_mul_rpow (L a b : ℝ) (hL : 0 < L) : L ^ a * L ^ b = L ^ (a + b) :=
  (Real.rpow_add hL a b).symm

/-- `L^a * L^b * L^c * L^d = L^{a+b+c+d}` for `L > 0`. -/
private theorem rpow_add4 (L a b c d : ℝ) (hL : 0 < L) :
    L ^ a * L ^ b * L ^ c * L ^ d = L ^ (a + b + c + d) := by
  rw [rpow_mul_rpow L a b hL, rpow_mul_rpow L (a + b) c hL,
    rpow_mul_rpow L (a + b + c) d hL]

/-- `H269 N A lam ≪ N^{3/8}` under the hypotheses of Theorem 3, provided `c₁ ≤ c₃`. -/
private theorem H269_le_three_eighths (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 c3 : ℝ)
    (hc1 : 0 ≤ c1) (hL : 1 ≤ Real.log N) (hA0 : 0 < A) (hAN : A ≤ N) (hq : 1 ≤ q)
    (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1))))
    (hAlow : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A) (hc13 : c1 ≤ c3) :
    H269 N A lam ≤ 20 * (N : ℝ) ^ (3 / 8 : ℝ) := by
  have hH := (H269_bounds N A lam q c1 hc1 hL hA0 hAN hq hlam).2
  have hN1 : (1 : ℝ) ≤ N := by
    by_contra h
    push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  -- `N/A ≤ N^{3/8} L^{-c₃}`
  have hNA : (N : ℝ) / A ≤ (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3) := by
    rw [div_le_iff₀ hA0]
    have hNp : (N : ℝ) ^ (3 / 8 : ℝ) * (N : ℝ) ^ (5 / 8 : ℝ) = N := by
      rw [← Real.rpow_add hNpos]
      rw [show (3 / 8 : ℝ) + 5 / 8 = 1 by norm_num, Real.rpow_one]
    have hLp : Real.log N ^ (-c3) * Real.log N ^ c3 = 1 := by
      rw [Real.rpow_neg (le_of_lt hL0)]
      exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hL0 c3))
    have hprod : ((N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3)) *
        ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3) = N := by
      calc ((N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3)) *
            ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3)
          = ((N : ℝ) ^ (3 / 8 : ℝ) * (N : ℝ) ^ (5 / 8 : ℝ)) *
            (Real.log N ^ (-c3) * Real.log N ^ c3) := by ring
        _ = N * 1 := by rw [hNp, hLp]
        _ = N := by ring
    calc (N : ℝ) = ((N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3)) *
          ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3) := hprod.symm
      _ ≤ ((N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3)) * A :=
          mul_le_mul_of_nonneg_left hAlow
            (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg (le_of_lt hL0) _))
  -- `N L^{c₁}/A ≤ N^{3/8}`
  have hmain : (N : ℝ) * Real.log N ^ c1 / A ≤ (N : ℝ) ^ (3 / 8 : ℝ) := by
    have hsplit : (N : ℝ) * Real.log N ^ c1 / A =
        ((N : ℝ) / A) * Real.log N ^ c1 := by ring
    rw [hsplit]
    have h1 : ((N : ℝ) / A) * Real.log N ^ c1 ≤
        ((N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3)) * Real.log N ^ c1 :=
      mul_le_mul_of_nonneg_right hNA (Real.rpow_nonneg (le_of_lt hL0) _)
    have hLpc : Real.log N ^ (-c3) * Real.log N ^ c1 = Real.log N ^ (c1 - c3) := by
      rw [rpow_mul_rpow (Real.log N) (-c3) c1 hL0]
      congr 1
      ring
    have h2 : ((N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3)) * Real.log N ^ c1 =
        (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - c3) := by
      calc ((N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3)) * Real.log N ^ c1
          = (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N ^ (-c3) * Real.log N ^ c1) := by ring
        _ = (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - c3) := by rw [hLpc]
    have h3 : Real.log N ^ (c1 - c3) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le hL (show c1 - c3 ≤ 0 by linarith)
      rwa [Real.rpow_zero] at h
    calc ((N : ℝ) / A) * Real.log N ^ c1
        ≤ ((N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (-c3)) * Real.log N ^ c1 := h1
      _ = (N : ℝ) ^ (3 / 8 : ℝ) * Real.log N ^ (c1 - c3) := h2
      _ ≤ (N : ℝ) ^ (3 / 8 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hN0 _)
      _ = (N : ℝ) ^ (3 / 8 : ℝ) := by ring
  calc H269 N A lam ≤ 20 * (N : ℝ) * Real.log N ^ c1 / A := hH
    _ = 20 * ((N : ℝ) * Real.log N ^ c1 / A) := by ring
    _ ≤ 20 * (N : ℝ) ^ (3 / 8 : ℝ) := by linarith

/-- `N²/A² ≤ N^{3/4} L^{-2c₃}` under `A ≥ N^{5/8} L^{c₃}`. -/
private theorem sq_div_sq_le (N : ℕ) (A : ℝ) (c3 : ℝ)
    (hL : 1 ≤ Real.log N) (hA0 : 0 < A)
    (hAlow : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A) :
    (N : ℝ) ^ 2 / A ^ 2 ≤ (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3) := by
  have hN1 : (1 : ℝ) ≤ N := by
    by_contra h
    push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hbase0 : (0 : ℝ) ≤ (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 :=
    mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg (le_of_lt hL0) _)
  have hA2pos : (0 : ℝ) < A ^ 2 := pow_pos hA0 2
  have hkey : (N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * c3) ≤ A ^ 2 := by
    have hs1 : ((N : ℝ) ^ (5 / 8 : ℝ)) ^ 2 = (N : ℝ) ^ (5 / 4 : ℝ) := by
      rw [pow_two, ← Real.rpow_add hNpos]
      norm_num
    have hs2 : (Real.log N ^ c3) ^ 2 = Real.log N ^ (2 * c3) := by
      rw [pow_two, ← Real.rpow_add hL0]
      congr 1
      ring
    have hsq : ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3) ^ 2 =
        (N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * c3) := by
      rw [mul_pow, hs1, hs2]
    rw [← hsq]
    exact pow_le_pow_left₀ hbase0 hAlow 2
  rw [div_le_iff₀ hA2pos]
  have hNp : (N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (5 / 4 : ℝ) = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_add hNpos]
    rw [show (3 / 4 : ℝ) + 5 / 4 = 2 by norm_num, Real.rpow_two]
  have hLp : Real.log N ^ (-2 * c3) * Real.log N ^ (2 * c3) = 1 := by
    rw [rpow_mul_rpow (Real.log N) (-2 * c3) (2 * c3) hL0]
    rw [show -2 * c3 + 2 * c3 = 0 by ring, Real.rpow_zero]
  have hprod : ((N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3)) *
      ((N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * c3)) = (N : ℝ) ^ 2 := by
    calc ((N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3)) *
          ((N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * c3))
        = ((N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (5 / 4 : ℝ)) *
          (Real.log N ^ (-2 * c3) * Real.log N ^ (2 * c3)) := by ring
      _ = (N : ℝ) ^ 2 * 1 := by rw [hNp, hLp]
      _ = (N : ℝ) ^ 2 := by ring
  calc (N : ℝ) ^ 2 = ((N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3)) *
        ((N : ℝ) ^ (5 / 4 : ℝ) * Real.log N ^ (2 * c3)) := hprod.symm
    _ ≤ ((N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3)) * A ^ 2 :=
        mul_le_mul_of_nonneg_left hkey
          (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg (le_of_lt hL0) _))

/-- `T269 N A lam q c₇ ≪ N^{3/4}` under the hypotheses of Theorem 3, provided
`c₁ + c₂ + c₇ ≤ 2 c₃`. -/
private theorem T269_le_three_quarters (N : ℕ) (A lam : ℝ) (q : ℕ) (c1 c2 c3 c7 : ℝ)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc7 : 0 ≤ c7) (hL : 1 ≤ Real.log N) (hA0 : 0 < A)
    (hAN : A ≤ N)
    (hq : 1 ≤ q) (hlam : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1))))
    (hAlow : (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c3 ≤ A)
    (hqc2 : (q : ℝ) ≤ Real.log N ^ c2) (hexp : c1 + c2 + c7 ≤ 2 * c3) :
    T269 N A lam q c7 ≤ 2 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  have hT := T269_bound N A lam q c1 c7 hc1 hL hA0 hAN hq hlam
  have hN1 : (1 : ℝ) ≤ N := by
    by_contra h
    push Not at h
    have : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h.le
    linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  -- `√q ≤ L^{c₂}`
  have hX1 : (1 : ℝ) ≤ Real.log N ^ c2 := Real.one_le_rpow hL hc2
  have hX0 : (0 : ℝ) ≤ Real.log N ^ c2 := by linarith
  have hsqrt : Real.sqrt q ≤ Real.log N ^ c2 := by
    rw [Real.sqrt_le_left hX0]
    have h1 : (q : ℝ) ≤ Real.log N ^ c2 := hqc2
    have h2 : Real.log N ^ c2 ≤ (Real.log N ^ c2) ^ 2 := by
      have h3 : Real.log N ^ c2 ≤ Real.log N ^ (2 * c2) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith)
      have h4 : (Real.log N ^ c2) ^ 2 = Real.log N ^ (2 * c2) := by
        rw [pow_two, rpow_mul_rpow (Real.log N) c2 c2 hL0]
        congr 1
        ring
      linarith
    linarith
  -- `N² L^{c₁}/A² ≤ N^{3/4} L^{c₁-2c₃}`
  have hsq := sq_div_sq_le N A c3 hL hA0 hAlow
  have hNsq : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3) :=
    mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg (le_of_lt hL0) _)
  have hA2 : (0 : ℝ) < A ^ 2 := pow_pos hA0 2
  have hmid : (N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2 ≤
      (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3) * Real.log N ^ c1 := by
    have hsplit : (N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2 =
        ((N : ℝ) ^ 2 / A ^ 2) * Real.log N ^ c1 := by ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (le_of_lt hL0) _)
  have hcomb : (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3) * Real.log N ^ c1 =
      (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (c1 + (-2 * c3)) := by
    have hp : Real.log N ^ (-2 * c3) * Real.log N ^ c1 = Real.log N ^ (c1 + (-2 * c3)) := by
      rw [rpow_mul_rpow (Real.log N) (-2 * c3) c1 hL0]
      congr 1
      ring
    calc (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3) * Real.log N ^ c1
        = (N : ℝ) ^ (3 / 4 : ℝ) * (Real.log N ^ (-2 * c3) * Real.log N ^ c1) := by ring
      _ = (N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (c1 + (-2 * c3)) := by rw [hp]
  have hexp2 : c1 + (-2 * c3) ≤ 0 := by linarith
  have hfin : Real.log N ^ (c1 + (-2 * c3)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hL hexp2
    rwa [Real.rpow_zero] at h
  calc T269 N A lam q c7
      ≤ 2 * Real.sqrt q * ((N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2) * Real.log N ^ c7 := hT
    _ ≤ 2 * Real.log N ^ c2 *
          ((N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3) * Real.log N ^ c1) *
          Real.log N ^ c7 := by
        have h2 : 0 ≤ 2 * Real.log N ^ c2 := by linarith
        have hc7 : 0 ≤ Real.log N ^ c7 := Real.rpow_nonneg (le_of_lt hL0) _
        calc 2 * Real.sqrt q * ((N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2) * Real.log N ^ c7
            ≤ 2 * Real.log N ^ c2 *
              ((N : ℝ) ^ 2 * Real.log N ^ c1 / A ^ 2) * Real.log N ^ c7 := by
                gcongr
          _ ≤ 2 * Real.log N ^ c2 *
              ((N : ℝ) ^ (3 / 4 : ℝ) * Real.log N ^ (-2 * c3) * Real.log N ^ c1) *
              Real.log N ^ c7 := by
                gcongr
    _ = 2 * (N : ℝ) ^ (3 / 4 : ℝ) *
          (Real.log N ^ (-2 * c3) * Real.log N ^ c1 * Real.log N ^ c2 *
            Real.log N ^ c7) := by ring
    _ = 2 * (N : ℝ) ^ (3 / 4 : ℝ) *
          Real.log N ^ (c1 + (-2 * c3) + c2 + c7) := by
        rw [rpow_add4 (Real.log N) (-2 * c3) c1 c2 c7 hL0,
          show -2 * c3 + c1 + c2 + c7 = c1 + (-2 * c3) + c2 + c7 by ring]
    _ ≤ 2 * (N : ℝ) ^ (3 / 4 : ℝ) * 1 := by
        have hfin2 : Real.log N ^ (c1 + (-2 * c3) + c2 + c7) ≤ 1 := by
          have h := Real.rpow_le_rpow_of_exponent_le hL (show c1 + (-2 * c3) + c2 + c7 ≤ 0 by
            linarith)
          rwa [Real.rpow_zero] at h
        gcongr
    _ = 2 * (N : ℝ) ^ (3 / 4 : ℝ) := by ring

open Filter Topology in
/-- The order of `L(s, χ)` at `s = 1` is `0`: `s = 1` is a pole of the principal character and
is not a zero of the others. (Local copy of what the split file proves; the file's imports do not
contain it.) -/
private theorem analyticOrderNat_LFunction_one_p (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    analyticOrderNatAt (DirichletCharacter.LFunction χ) 1 = 0 := by
  by_cases hχ : χ = 1
  · subst hχ
    apply analyticOrderNatAt_of_not_analyticAt
    intro han
    have hc : ContinuousAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) 1 :=
      han.continuousAt
    have h0 : Tendsto
        (fun s : ℂ => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
        (𝓝[≠] 1) (𝓝 0) := by
      have : Tendsto
          (fun s : ℂ => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)
          (𝓝 1) (𝓝 ((1 - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) 1)) :=
        ((continuous_id.sub continuous_const).continuousAt.tendsto).mul hc.tendsto
      simpa using this.mono_left nhdsWithin_le_nhds
    have hr := DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
    have heq := tendsto_nhds_unique hr h0
    have hne : ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      have h2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      intro h
      have h1 : (p : ℂ)⁻¹ = 1 := by linear_combination -h
      have h2' : (p : ℂ) = 1 := by simpa using congrArg (·⁻¹) h1
      have h3 : (p : ℝ) = 1 := by exact_mod_cast h2'
      linarith
    exact hne heq
  · unfold analyticOrderNatAt
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (DirichletCharacter.LFunction_apply_one_ne_zero hχ))]
    rfl

/-- Page 269, "by Lemma 5" at the level of the count: no zero in the window other than `s = 1`
gives count `0`. (Local copy of the split file's `zeroCountZ_eq_zero_of_free`.) -/
private theorem zeroCountZ_eq_zero_of_free_p (q : ℕ) [NeZero q] (α T H : ℝ)
    (hfree : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), ρ ≠ 1 →
      DirichletCharacter.LFunction χ ρ = 0 → α ≤ ρ.re → T ≤ ρ.im → ρ.im ≤ T + H → False) :
    zeroCountZ α T H q = 0 := by
  unfold zeroCountZ
  apply Finset.sum_eq_zero
  intro χ _
  apply finsum_mem_eq_zero_of_forall_eq_zero
  intro ρ hρ
  by_cases h1 : ρ = 1
  · subst h1
    simp [analyticOrderNat_LFunction_one_p q χ]
  · exact (hfree χ ρ h1 hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2).elim

/-- LEAF: Page 269, "by Lemma 5": above `beta5` the count is `0`. MEDIUM. Apply Lemma 5 at height
`N`, where `q ≤ L^{c₂}`; the window `[T₁, T₁ + H]` lies in `|t| ≤ N` by `T269_bound` and
`H269_bounds`; then `zeroCountZ_eq_zero_of_free` of SPLIT_theorem3_p2_1122. -/
theorem highFree_of_lemma5 (h5 : Lemma5NoExc) : ∃ c0 : ℝ, 0 < c0 ∧ HighFreePart c0 := by
  obtain ⟨c0, hc0, h5'⟩ := h5
  refine ⟨c0, hc0, ?_⟩
  intro c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨T0, hT0⟩ := h5' c2 hc2
  refine ⟨c1 + c7 + c2 + 10, by linarith, max (max T0 (Real.exp 1)) 4096, ?_⟩
  intro N A α lam a q _ hN hAlow hAN hcond hqc2 hlam β T1 hβ hT1
  have h4096N : (4096 : ℝ) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hexp1 : Real.exp 1 ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hT0N : T0 ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) hexp1
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hq1 : 1 ≤ q := hcond.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hAp : (0 : ℝ) < (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c7 + c2 + 10) :=
    mul_pos (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hL0 _)
  have hA0 : 0 < A := lt_of_lt_of_le hAp hAlow
  have hH : H269 N A lam ≤ 20 * (N : ℝ) ^ (3 / 8 : ℝ) :=
    H269_le_three_eighths N A lam q c1 (c1 + c7 + c2 + 10) hc1.le hL1 hA0 hAN hq1
      hcond.2.2.1 hAlow (by linarith)
  have hT : T269 N A lam q c7 ≤ 2 * (N : ℝ) ^ (3 / 4 : ℝ) :=
    T269_le_three_quarters N A lam q c1 c2 (c1 + c7 + c2 + 10) c7 hc1.le hc2.le hc7.le
      hL1 hA0 hAN hq1 hcond.2.2.1 hAlow hqc2 (by linarith)
  have hH0 : 0 ≤ H269 N A lam := by
    unfold H269
    have h1 : 0 ≤ (N : ℝ) / A := div_nonneg hN0 hA0.le
    have h2 : 0 ≤ |lam| * A := mul_nonneg (abs_nonneg _) hA0.le
    linarith
  have hfit : |T1| + |H269 N A lam| ≤ (N : ℝ) := by
    rw [abs_of_nonneg hH0]
    have h4 : 4 * (N : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) / 2 := four_rpow_le N h4096N
    have h20 : 20 * (N : ℝ) ^ (3 / 8 : ℝ) ≤ (N : ℝ) / 2 := twenty_rpow_le N h4096N
    linarith
  refine zeroCountZ_eq_zero_of_free_p q β T1 (H269 N A lam) ?_
  intro χ ρ hρ1 hLρ hβre him1 him2
  have him : |ρ.im| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le T1, le_abs_self T1, abs_nonneg (H269 N A lam)]
    · linarith [le_abs_self T1, le_abs_self (H269 N A lam), abs_nonneg (H269 N A lam)]
  have hlt := hT0 q (N : ℝ) hT0N hqc2 χ ρ hρ1 hLρ him
  have hb : ρ.re < beta5 c0 N q := by
    unfold beta5
    exact hlt
  linarith

/-- `log L ≤ ε L^s` eventually, for `ε > 0` and `s > 0`. -/
private theorem eventually_log_le_smul_rpow_gen (s cc : ℝ) (hs : 0 < s) (hcc : 0 < cc) :
    ∀ᶠ L : ℝ in Filter.atTop, Real.log L ≤ cc * L ^ s := by
  have h := isLittleO_log_rpow_atTop hs
  have h2 := h.def hcc
  rw [Filter.eventually_atTop] at h2
  obtain ⟨a, ha⟩ := h2
  refine Filter.eventually_atTop.mpr ⟨max a 1, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxa : a ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hb := ha x hxa
  have hlogn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxr : 0 ≤ x ^ s := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogn, abs_of_nonneg hxr] at hb
  exact hb

/-- `log L ≤ ε L^{1/5}` eventually, for any `ε > 0`. -/
private theorem eventually_log_le_smul_rpow (cc : ℝ) (hcc : 0 < cc) :
    ∀ᶠ L : ℝ in Filter.atTop, Real.log L ≤ cc * L ^ (1 / 5 : ℝ) :=
  eventually_log_le_smul_rpow_gen (1 / 5) cc (by norm_num) hcc

/-- `(log x)^a ≤ x^r` eventually, for `a ≥ 0` and `r > 0`. -/
private theorem eventually_log_rpow_le_rpow (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ a ≤ x ^ r := by
  have hs : (0 : ℝ) < r / (a + 1) := by positivity
  have hsmall := eventually_log_le_smul_rpow_gen (r / (a + 1)) 1 hs (by norm_num)
  have hone : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  filter_upwards [hsmall, hone] with x hx hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxr : 0 ≤ x ^ (r / (a + 1)) := Real.rpow_nonneg hx0.le _
  have step1 : Real.log x ^ a ≤ (x ^ (r / (a + 1))) ^ a :=
    Real.rpow_le_rpow hlogn (by simpa using hx) ha
  have step2 : (x ^ (r / (a + 1))) ^ a = x ^ (r / (a + 1) * a) := by
    rw [← Real.rpow_mul hx0.le]
  have step3 : x ^ (r / (a + 1) * a) ≤ x ^ r := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have h1 : (0 : ℝ) < a + 1 := by linarith
    rw [div_mul_eq_mul_div]
    rw [div_le_iff₀ h1]
    nlinarith
  calc Real.log x ^ a ≤ (x ^ (r / (a + 1))) ^ a := step1
    _ = x ^ (r / (a + 1) * a) := step2
    _ ≤ x ^ r := step3

/-- `L^E * exp (-c L^{1/5}) ≤ 1` eventually. -/
private theorem eventually_rpow_mul_exp_le_one (c E : ℝ) (hc : 0 < c) (hE : 0 < E) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ E * Real.exp (-(c * L ^ (1 / 5 : ℝ))) ≤ 1 := by
  have hlog := eventually_log_le_smul_rpow (c / E) (by positivity)
  have hone : ∀ᶠ L : ℝ in Filter.atTop, (1 : ℝ) ≤ L := Filter.eventually_ge_atTop 1
  filter_upwards [hlog, hone] with L hL hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hexp : L ^ E = Real.exp (Real.log L * E) := Real.rpow_def_of_pos hL0 E
  have hce : E * (c / E) = c := by field_simp
  have h2 : E * (c / E * L ^ (1 / 5 : ℝ)) = c * L ^ (1 / 5 : ℝ) := by
    rw [← mul_assoc, hce]
  have harg : Real.log L * E + -(c * L ^ (1 / 5 : ℝ)) ≤ 0 := by
    have h1 : E * Real.log L ≤ E * (c / E * L ^ (1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hL hE.le
    linarith
  calc L ^ E * Real.exp (-(c * L ^ (1 / 5 : ℝ)))
      = Real.exp (Real.log L * E + -(c * L ^ (1 / 5 : ℝ))) := by
        rw [hexp, ← Real.exp_add]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr harg
    _ = 1 := Real.exp_zero

open Filter Topology in
/-- Every point has a punctured neighbourhood free of zeros of `L(s, χ)`. (Local copy of
`lfun_isolated`.) -/
private theorem lfun_isolated_p (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℂ) :
    ∀ᶠ w in 𝓝 z, w ≠ z → DirichletCharacter.LFunction χ w ≠ 0 := by
  set f := DirichletCharacter.LFunction χ
  refine eventually_nhdsWithin_iff.mp ?_
  by_cases hz : z = 1 ∧ χ = 1
  · obtain ⟨rfl, rfl⟩ := hz
    have hr := DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
    have hne : ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp h
      have h2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have h3 : (p : ℂ)⁻¹ = 1 := by linear_combination -h
      have h4 : (p : ℂ) = 1 := by simpa using congrArg (·⁻¹) h3
      have h5 : (p : ℝ) = 1 := by exact_mod_cast h4
      linarith
    filter_upwards [hr.eventually_ne hne] with w hw
    intro h0
    exact hw (mul_eq_zero.mpr (Or.inr h0))
  · have hdiff : DifferentiableOn ℂ f {1}ᶜ := fun w hw =>
      (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw)).differentiableWithinAt
    have hanU : AnalyticOnNhd ℂ f {1}ᶜ := hdiff.analyticOnNhd isOpen_compl_singleton
    have hanz : AnalyticAt ℂ f z := by
      by_cases h1 : z = 1
      · have hχ : χ ≠ 1 := fun h => hz ⟨h1, h⟩
        exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
      · exact hanU z h1
    rcases hanz.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
        (isConnected_compl_singleton_of_one_lt_rank
          (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected
      have hz' : ∃ w : ℂ, w ≠ 1 ∧ f =ᶠ[𝓝 w] 0 := by
        by_cases h1 : z = 1
        · have hev : ∀ᶠ w in 𝓝 z, ∀ᶠ y in 𝓝 w, f y = 0 := h.eventually_nhds
          have hne : ∀ᶠ w in 𝓝[≠] z, w ≠ 1 := by
            subst h1; exact self_mem_nhdsWithin
          obtain ⟨w, hw1, hw2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and hne).exists
          exact ⟨w, hw2, hw1⟩
        · exact ⟨z, h1, h⟩
      obtain ⟨w, hw1, hw⟩ := hz'
      have hEq := hanU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hw1 hw
      have h2 : f 2 = 0 := hEq (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
        (by norm_num) h2
    · exact h

/-- Page 262, Lemma 4: the zeros of `L(s, χ)` in the window are finitely many. (Local copy of
`zeroWindow_finite_proof`.) -/
private theorem zeroWindow_finite_p (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (α T H : ℝ) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
      ρ.im ≤ T + H}.Finite := by
  set f := DirichletCharacter.LFunction χ
  set S := {ρ : ℂ | f ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H}
  set Kk := Complex.equivRealProdCLM.symm '' (Set.Icc α 1 ×ˢ Set.Icc T (T + H))
  have hK : IsCompact Kk :=
    (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hSK : S ⊆ Kk := by
    intro ρ hρ
    refine ⟨(ρ.re, ρ.im), ⟨⟨hρ.2.1, ?_⟩, hρ.2.2.1, hρ.2.2.2⟩, ?_⟩
    · by_contra hlt
      push Not at hlt
      have hne : ρ ≠ 1 := by
        intro h; rw [h] at hlt; simp at hlt
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hne) hlt.le hρ.1
    · rfl
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover
    (fun z => {w | w ≠ z → f w ≠ 0}) (fun z _ => lfun_isolated_p q χ z)
  refine (t.finite_toSet).subset ?_
  intro ρ hρ
  obtain ⟨z, hzt, hz⟩ := Set.mem_iUnion₂.mp (hcover (hSK hρ))
  by_contra hnot
  have : ρ ≠ z := fun h => hnot (h ▸ hzt)
  exact hz this hρ.1

/-- The count `N(α, T, H, q)` is monotone in `H`. (Local copy of `zeroCountZ_mono_H_of`.) -/
private theorem zeroCountZ_mono_H_of_p (q : ℕ) [NeZero q] (α T H H' : ℝ) (hH : H ≤ H')
    (hfinite : ∀ χ : DirichletCharacter ℂ q, {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      α ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ T + H'}.Finite) :
    zeroCountZ α T H q ≤ zeroCountZ α T H' q := by
  unfold zeroCountZ
  apply Finset.sum_le_sum
  intro χ _
  set s := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
      ρ.im ≤ T + H}
  set s' := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ α ≤ ρ.re ∧ T ≤ ρ.im ∧
      ρ.im ≤ T + H'}
  have hss : s ⊆ s' := by
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans (by linarith)⟩
  have hfin : s'.Finite := hfinite χ
  set g := fun ρ : ℂ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
  have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ => Nat.cast_nonneg _
  rw [finsum_mem_def, finsum_mem_def]
  apply finsum_le_finsum
  · exact (hfin.subset hss).subset (Set.support_indicator_subset)
  · exact hfin.subset (Set.support_indicator_subset)
  · intro ρ
    exact Set.indicator_le_indicator_of_subset hss hg0 ρ

/-- `N(α, T, H, q)` is monotone in `H`. -/
private theorem zeroCountZ_mono_H_p (q : ℕ) [NeZero q] (α T H H' : ℝ) (hH : H ≤ H') :
    zeroCountZ α T H q ≤ zeroCountZ α T H' q :=
  zeroCountZ_mono_H_of_p q α T H H' hH fun χ => zeroWindow_finite_p q χ α T H'

/-- `(x^a)^e = x^{a e}` for `x ≥ 0`. -/
private theorem rpow_mul_rpow' (x a e : ℝ) (hx : 0 ≤ x) : (x ^ a) ^ e = x ^ (a * e) :=
  (Real.rpow_mul hx a e).symm

/-- `(x y z)^e = x^e y^e z^e` for nonnegative `x, y, z`. -/
private theorem mul_rpow_three (x y z e : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x * y * z) ^ e = x ^ e * y ^ e * z ^ e := by
  rw [Real.mul_rpow (mul_nonneg hx hy) hz, Real.mul_rpow hx hy]

set_option maxHeartbeats 1000000 in
/-- LEAF: Page 269, "by (2.4)": the density part for every `c₀ > 0`. MEDIUM. Enlarge the window to
`H' = H + |T₁|^{1/3} + 2` with `zeroCountZ_mono_H_proof`, apply (2.4), use `H' ≪ N^{3/8} L^{c₁}`
from `H269_bounds` and `T269_bound`, so `q^{12/5} H'^{12/5} N⁻¹ ≤ N^{-1/20}` for large `N`, and
`1 - β > c₀/(2 L^{4/5})` below `beta5`. -/
theorem highDensity_of_24 (h24 : Lemma4Eq24) (c0 : ℝ) (hc0 : 0 < c0) :
    HighDensityPart c0 := by
  obtain ⟨c00, hc00, K, hK⟩ := h24
  intro c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp
    (eventually_log_le_smul_rpow_gen (4 / 5) (1 / c2) (by norm_num) (by positivity))
  obtain ⟨NE, hNE⟩ := Filter.eventually_atTop.mp
    (eventually_rpow_mul_exp_le_one (c0 / 30) (c2 + c00 + B + 1) (by positivity) (by linarith))
  refine ⟨c1 + c2 + c7 + 20, by linarith,
    max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) + 1,
    max (Real.exp (max (max NL NE) 52)) (max 4096 4), ?_⟩
  intro N A α lam a q _ hN hAlow hAN hcond hqc2 hlam β T1 hβ5 hβbeta hT1
  -- thresholds from the eventual statements
  have hexpL : Real.exp (max (max NL NE) 52) ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have h4096 : (4096 : ℝ) ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNne : N ≠ 0 := by rintro rfl; norm_num at h4096
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hNne
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hLbig : max (max NL NE) 52 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos (max (max NL NE) 52)) hexpL
    rwa [Real.log_exp] at h
  have hL1 : 1 ≤ Real.log N :=
    le_trans (le_trans (by norm_num : (1 : ℝ) ≤ 52) (le_max_right _ _)) hLbig
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hL52 : 52 ≤ Real.log N := le_trans (le_max_right _ _) hLbig
  have hLNL : NL ≤ Real.log N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLbig
  have hLNE : NE ≤ Real.log N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLbig
  have hlogL : Real.log (Real.log N) ≤ 1 / c2 * (Real.log N) ^ (4 / 5 : ℝ) := hNL _ hLNL
  have hdecay := hNE _ hLNE
  -- the hypotheses of Theorem 3
  have hq1 : 1 ≤ q := hcond.2.2.2.1
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlamR : |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1))) := hcond.2.2.1
  have hAp : (0 : ℝ) < (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ (c1 + c2 + c7 + 20) :=
    mul_pos (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hL0 _)
  have hA0 : 0 < A := lt_of_lt_of_le hAp hAlow
  have hHb := H269_bounds N A lam q c1 hc1.le hL1 hA0 hAN hq1 hlamR
  have hH10 : 10 ≤ H269 N A lam := hHb.1
  have hHle : H269 N A lam ≤ 20 * (N : ℝ) ^ (3 / 8 : ℝ) :=
    H269_le_three_eighths N A lam q c1 (c1 + c2 + c7 + 20) hc1.le hL1 hA0 hAN hq1 hlamR
      hAlow (by linarith)
  have hTle : T269 N A lam q c7 ≤ 2 * (N : ℝ) ^ (3 / 4 : ℝ) :=
    T269_le_three_quarters N A lam q c1 c2 (c1 + c2 + c7 + 20) c7 hc1.le hc2.le hc7.le hL1
      hA0 hAN hq1 hlamR hAlow hqc2 (by linarith)
  have hT1le : |T1| ≤ 4 * (N : ℝ) ^ (3 / 4 : ℝ) := by linarith
  -- `|T₁|^{1/3} ≤ 4 N^{1/4} ≤ 4 N^{3/8}`
  have hcube : |T1| ^ (1 / 3 : ℝ) ≤ 4 * (N : ℝ) ^ (3 / 8 : ℝ) := by
    have hN38 : (1 : ℝ) ≤ (N : ℝ) ^ (3 / 8 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have h1 : |T1| ^ (1 / 3 : ℝ) ≤ (4 * (N : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) hT1le (by norm_num)
    have h2 : (4 * (N : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / 3 : ℝ) =
        4 ^ (1 / 3 : ℝ) * ((N : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / 3 : ℝ) :=
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0 _)
    have h3 : ((N : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / 3 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [rpow_mul_rpow' (N : ℝ) (3 / 4) (1 / 3) hN0]
      norm_num
    have h4 : (4 : ℝ) ^ (1 / 3 : ℝ) ≤ 4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
        (by norm_num : (1 / 3 : ℝ) ≤ 1)
      rwa [Real.rpow_one] at h
    have h5 : (4 : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) ≤ 4 * (N : ℝ) ^ (3 / 8 : ℝ) := by
      have h6 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (3 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      have h7 : 0 < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hNpos _
      nlinarith [h4, h6, h7, Real.rpow_nonneg hN0 (1 / 4 : ℝ),
        Real.rpow_nonneg hN0 (3 / 8 : ℝ)]
    calc |T1| ^ (1 / 3 : ℝ) ≤ (4 * (N : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / 3 : ℝ) := h1
      _ = 4 ^ (1 / 3 : ℝ) * ((N : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / 3 : ℝ) := h2
      _ = 4 ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by rw [h3]
      _ ≤ 4 * (N : ℝ) ^ (3 / 8 : ℝ) := h5
  have hH'0 : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 8 : ℝ) := Real.rpow_nonneg hN0 _
  have hH'1 : (1 : ℝ) ≤ (N : ℝ) ^ (3 / 8 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hH'le : H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2 ≤ 26 * (N : ℝ) ^ (3 / 8 : ℝ) := by
    linarith
  have hH'2 : 2 ≤ H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2 := by
    have := Real.rpow_nonneg (abs_nonneg T1) (1 / 3 : ℝ); linarith
  have hH'13 : |T1| ^ (1 / 3 : ℝ) ≤ H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2 := by linarith
  have hH'pos : 0 < H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2 := by linarith
  have hβ1 : β ≤ 1 := by
    have h := beta5_lt_one c0 hc0 N q
    linarith
  have hσpos : 0 < 1 - β := by
    have h := beta5_lt_one c0 hc0 N q
    linarith
  -- (2.4) on the enlarged window, monotone in the window length
  have hmono : zeroCountZ β T1 (H269 N A lam) q ≤
      zeroCountZ β T1 (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2) q := by
    have h := Real.rpow_nonneg (abs_nonneg T1) (1 / 3 : ℝ)
    exact zeroCountZ_mono_H_p q β T1 (H269 N A lam) _ (by linarith)
  have hcount : zeroCountZ β T1 (H269 N A lam) q ≤
      K * ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ ((12 / 5) * (1 - β)) *
        Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00 :=
    hmono.trans (hK q β T1 (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2) hH'2 hH'13 hβ5 hβ1)
  -- `q H' ≤ 52 N^{3/8} L^{c2}`
  have hH'nonneg : (0 : ℝ) ≤ H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2 := by linarith
  have hqH : (q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2) ≤
      52 * (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2 := by
    have h1 : (q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2) ≤
        (Real.log N) ^ c2 * (26 * (N : ℝ) ^ (3 / 8 : ℝ)) :=
      mul_le_mul hqc2 hH'le (by linarith) (Real.rpow_nonneg hL0.le _)
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2 :=
      mul_nonneg hH'0 (Real.rpow_nonneg hL0.le _)
    have h3 : (Real.log N) ^ c2 * (26 * (N : ℝ) ^ (3 / 8 : ℝ)) =
        26 * ((N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) := by ring
    have h4 : 26 * ((N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) ≤
        52 * ((N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) :=
      mul_le_mul_of_nonneg_right (by norm_num) h2
    have h5 : 52 * ((N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) =
        52 * (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2 := by ring
    linarith [h1, h3, h4, h5]
  have hqHpos : 0 < (q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2) :=
    mul_pos hqpos hH'pos
  have hqH1 : 1 ≤ (q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2) := by
    have h := mul_le_mul hqR (by linarith : (1 : ℝ) ≤ H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)
      (by norm_num) (by linarith : (0 : ℝ) ≤ (q : ℝ))
    linarith [h]
  -- `log (q H') ≤ (c₂ + 2) L`
  have hlogqH : Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ≤
      (c2 + 2) * Real.log N := by
    have h1 : Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ≤
        Real.log (52 * (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) :=
      Real.log_le_log hqHpos hqH
    have h2 : Real.log (52 * (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) =
        Real.log 52 + (3 / 8) * Real.log N + c2 * Real.log (Real.log N) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_rpow hNpos,
        Real.log_rpow hL0]
    have h3 : Real.log 52 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log (Real.log N) ≤ Real.log N := Real.log_le_self hL0.le
    have h5 : c2 * Real.log (Real.log N) ≤ c2 * Real.log N :=
      mul_le_mul_of_nonneg_left h4 hc2.le
    rw [h2] at h1
    have h6 : Real.log 52 + (3 / 8) * Real.log N + c2 * Real.log (Real.log N) ≤
        Real.log N + (3 / 8) * Real.log N + c2 * Real.log N := by linarith [h3, h5]
    have h7 : Real.log N + (3 / 8) * Real.log N + c2 * Real.log N = (c2 + 11 / 8) * Real.log N := by
      ring
    have h8 : (c2 + 11 / 8) * Real.log N ≤ (c2 + 2) * Real.log N := by nlinarith [hL0]
    linarith [h1, h6, h7, h8]
  have hlogqH_nonneg : (0 : ℝ) ≤ Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) :=
    Real.log_nonneg hqH1
  -- the exponent bookkeeping
  have he0 : (0 : ℝ) ≤ (12 / 5) * (1 - β) := by linarith
  have he25 : (12 / 5) * (1 - β) ≤ 2 / 5 := by linarith
  have hexp : ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ ((12 / 5) * (1 - β)) ≤
      (52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) * (Real.log N) ^ c2 := by
    have hbase0 : (0 : ℝ) ≤ (q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2) := by linarith
    have hstep1 : ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ ((12 / 5) * (1 - β)) ≤
        (52 * (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) ^ ((12 / 5) * (1 - β)) :=
      Real.rpow_le_rpow hbase0 hqH he0
    have hstep2 : (52 * (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) ^ ((12 / 5) * (1 - β)) =
        (52 : ℝ) ^ ((12 / 5) * (1 - β)) * ((N : ℝ) ^ (3 / 8 : ℝ)) ^ ((12 / 5) * (1 - β)) *
          ((Real.log N) ^ c2) ^ ((12 / 5) * (1 - β)) :=
      mul_rpow_three _ _ _ _ (by norm_num) (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hL0.le _)
    have hstep3 : ((N : ℝ) ^ (3 / 8 : ℝ)) ^ ((12 / 5) * (1 - β)) = (N : ℝ) ^ ((9 / 10) * (1 - β)) := by
      rw [rpow_mul_rpow' (N : ℝ) (3 / 8) ((12 / 5) * (1 - β)) hN0]
      congr 1
      ring
    have hstep4 : ((Real.log N) ^ c2) ^ ((12 / 5) * (1 - β)) =
        (Real.log N) ^ (c2 * ((12 / 5) * (1 - β))) :=
      rpow_mul_rpow' (Real.log N) c2 _ hL0.le
    have hstep5 : (52 : ℝ) ^ ((12 / 5) * (1 - β)) ≤ (52 : ℝ) ^ (2 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he25
    have hstep6 : (Real.log N) ^ (c2 * ((12 / 5) * (1 - β))) ≤ (Real.log N) ^ c2 :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith [he25, hc2, he0])
    have hN9 : (0 : ℝ) ≤ (N : ℝ) ^ ((9 / 10) * (1 - β)) := Real.rpow_nonneg hN0 _
    have h52 : (0 : ℝ) ≤ (52 : ℝ) ^ (2 / 5 : ℝ) := by positivity
    have hLc2 : (0 : ℝ) ≤ (Real.log N) ^ c2 := Real.rpow_nonneg hL0.le _
    calc ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ ((12 / 5) * (1 - β))
        ≤ (52 * (N : ℝ) ^ (3 / 8 : ℝ) * (Real.log N) ^ c2) ^ ((12 / 5) * (1 - β)) := hstep1
      _ = (52 : ℝ) ^ ((12 / 5) * (1 - β)) * ((N : ℝ) ^ (3 / 8 : ℝ)) ^ ((12 / 5) * (1 - β)) *
            ((Real.log N) ^ c2) ^ ((12 / 5) * (1 - β)) := hstep2
      _ = (52 : ℝ) ^ ((12 / 5) * (1 - β)) * (N : ℝ) ^ ((9 / 10) * (1 - β)) *
            (Real.log N) ^ (c2 * ((12 / 5) * (1 - β))) := by rw [hstep3, hstep4]
      _ ≤ (52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) * (Real.log N) ^ c2 := by
          have hA1 : (52 : ℝ) ^ ((12 / 5) * (1 - β)) * (N : ℝ) ^ ((9 / 10) * (1 - β)) ≤
              (52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) :=
            mul_le_mul_of_nonneg_right hstep5 hN9
          have hA2 : (52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) *
              (Real.log N) ^ (c2 * ((12 / 5) * (1 - β))) ≤
              (52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) * (Real.log N) ^ c2 :=
            mul_le_mul_of_nonneg_left hstep6 (by positivity)
          calc (52 : ℝ) ^ ((12 / 5) * (1 - β)) * (N : ℝ) ^ ((9 / 10) * (1 - β)) *
                (Real.log N) ^ (c2 * ((12 / 5) * (1 - β)))
              ≤ (52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) *
                (Real.log N) ^ (c2 * ((12 / 5) * (1 - β))) := by
                exact mul_le_mul_of_nonneg_right hA1 (Real.rpow_nonneg hL0.le _)
            _ ≤ _ := hA2
  -- the `log` power
  have hlogpow : Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00 ≤
      (c2 + 2) ^ c00 * (Real.log N) ^ c00 := by
    have h1 : Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00 ≤
        ((c2 + 2) * Real.log N) ^ c00 :=
      Real.rpow_le_rpow hlogqH_nonneg hlogqH hc00.le
    have h2 : ((c2 + 2) * Real.log N) ^ c00 = (c2 + 2) ^ c00 * (Real.log N) ^ c00 :=
      Real.mul_rpow (by linarith) hL0.le
    rw [h2] at h1
    exact h1
  -- the decay of `N^{-(1-β)/10}`
  have hDpos : (0 : ℝ) < Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) := by
    have h1 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hqR
    have h2 : (1 : ℝ) < (N : ℝ) + 2 := by linarith
    have h3 : (0 : ℝ) < Real.log ((N : ℝ) + 2) := Real.log_pos h2
    have h4 : (0 : ℝ) < Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos h3 _
    linarith
  have hlogq : Real.log q ≤ (Real.log N) ^ (4 / 5 : ℝ) := by
    have h1 : Real.log q ≤ Real.log ((Real.log N) ^ c2) :=
      Real.log_le_log hqpos hqc2
    rw [Real.log_rpow hL0] at h1
    have h2 : c2 * Real.log (Real.log N) ≤ c2 * (1 / c2 * (Real.log N) ^ (4 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogL hc2.le
    have h3 : c2 * (1 / c2 * (Real.log N) ^ (4 / 5 : ℝ)) = (Real.log N) ^ (4 / 5 : ℝ) := by
      rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hc2), one_mul]
    linarith
  have hlogN2 : Real.log ((N : ℝ) + 2) ≤ 2 * Real.log N := by
    have h1 : (N : ℝ) + 2 ≤ 2 * (N : ℝ) := by linarith
    have h2 : Real.log ((N : ℝ) + 2) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by linarith) h1
    have h3 : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
      Real.log_mul (by norm_num) (by linarith)
    have h4 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
    rw [h3] at h2
    linarith
  have hD3 : Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) ≤
      3 * (Real.log N) ^ (4 / 5 : ℝ) := by
    have hLn : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
      (Real.log_pos (by linarith : (1 : ℝ) < (N : ℝ) + 2)).le
    have h5 : Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ) ≤ (2 * Real.log N) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow hLn hlogN2 (by norm_num)
    have h6 : (2 * Real.log N) ^ (4 / 5 : ℝ) = (2 : ℝ) ^ (4 / 5 : ℝ) * (Real.log N) ^ (4 / 5 : ℝ) :=
      Real.mul_rpow (by norm_num) hL0.le
    have h7 : (2 : ℝ) ^ (4 / 5 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (4 / 5 : ℝ) ≤ 1)
      rwa [Real.rpow_one] at h
    have h8 : (0 : ℝ) ≤ (Real.log N) ^ (4 / 5 : ℝ) := Real.rpow_nonneg hL0.le _
    have h9 : (2 : ℝ) ^ (4 / 5 : ℝ) * (Real.log N) ^ (4 / 5 : ℝ) ≤
        2 * (Real.log N) ^ (4 / 5 : ℝ) := mul_le_mul_of_nonneg_right h7 h8
    rw [h6] at h5
    linarith
  have hσlow : c0 / (3 * (Real.log N) ^ (4 / 5 : ℝ)) ≤ 1 - β := by
    have h1 : c0 / (Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ)) < 1 - β := by
      have h := hβbeta
      unfold beta5 at h
      linarith
    have h2 : c0 / (3 * (Real.log N) ^ (4 / 5 : ℝ)) ≤
        c0 / (Real.log q + Real.log ((N : ℝ) + 2) ^ (4 / 5 : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) hDpos]
      nlinarith [hD3]
    linarith
  have hsplit : Real.log N / (Real.log N) ^ (4 / 5 : ℝ) = (Real.log N) ^ (1 / 5 : ℝ) := by
    have h := Real.rpow_sub hL0 (1 : ℝ) (4 / 5 : ℝ)
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) - 4 / 5 = 1 / 5 by norm_num] at h
    rw [← h]
  have hNdecay : (N : ℝ) ^ (-(1 - β) / 10) ≤ Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ))) := by
    have hkey : c0 / (3 * (Real.log N) ^ (4 / 5 : ℝ)) * (Real.log N / 10) ≤
        (1 - β) * (Real.log N / 10) :=
      mul_le_mul_of_nonneg_right hσlow (by positivity)
    have heq : c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ) =
        c0 / (3 * (Real.log N) ^ (4 / 5 : ℝ)) * (Real.log N / 10) := by
      rw [← hsplit]
      field_simp
      ring
    have hexp2 : (N : ℝ) ^ (-(1 - β) / 10) = Real.exp (Real.log N * (-(1 - β) / 10)) := by
      rw [Real.rpow_def_of_pos hNpos]
    rw [hexp2]
    apply Real.exp_le_exp.mpr
    have heq2 : (1 - β) * (Real.log N / 10) = -(Real.log N * (-(1 - β) / 10)) := by ring
    linarith [hkey]
  -- assemble
  have hmul : (N : ℝ) ^ (β - 1) * (N : ℝ) ^ ((9 / 10) * (1 - β)) = (N : ℝ) ^ (-(1 - β) / 10) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hLcomb : (Real.log N) ^ c2 * (Real.log N) ^ c00 = (Real.log N) ^ (c2 + c00) :=
    rpow_mul_rpow (Real.log N) c2 c00 hL0
  have hid : (Real.log N) ^ (c2 + c00) =
      (Real.log N) ^ (-B - 1) * (Real.log N) ^ (c2 + c00 + B + 1) := by
    rw [rpow_mul_rpow (Real.log N) (-B - 1) (c2 + c00 + B + 1) hL0]
    congr 1
    ring
  have hKle : K ≤ max K 0 := le_max_left _ _
  have hinner : (N : ℝ) ^ (β - 1) *
      ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ ((12 / 5) * (1 - β)) *
        Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00 ≤
      (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1) := by
    have h1 : (N : ℝ) ^ (β - 1) *
        ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ ((12 / 5) * (1 - β)) *
          Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00 ≤
        (N : ℝ) ^ (β - 1) *
          ((52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) * (Real.log N) ^ c2) *
            ((c2 + 2) ^ c00 * (Real.log N) ^ c00) := by
      have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (β - 1) := Real.rpow_nonneg hN0 _
      have hX : (0 : ℝ) ≤ (52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) * (Real.log N) ^ c2 :=
        mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hN0 _)) (Real.rpow_nonneg hL0.le _)
      have hY : (0 : ℝ) ≤ (c2 + 2) ^ c00 * (Real.log N) ^ c00 :=
        mul_nonneg (by positivity) (Real.rpow_nonneg hL0.le _)
      calc (N : ℝ) ^ (β - 1) *
            ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ ((12 / 5) * (1 - β)) *
              Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00
          = (N : ℝ) ^ (β - 1) * (((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^
              ((12 / 5) * (1 - β)) *
              Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00) := by ring
        _ ≤ (N : ℝ) ^ (β - 1) * (((52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) *
              (Real.log N) ^ c2) * ((c2 + 2) ^ c00 * (Real.log N) ^ c00)) := by
              apply mul_le_mul_of_nonneg_left _ hNp
              exact mul_le_mul hexp hlogpow (Real.rpow_nonneg hlogqH_nonneg c00) hX
        _ = (N : ℝ) ^ (β - 1) * ((52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) *
              (Real.log N) ^ c2) * ((c2 + 2) ^ c00 * (Real.log N) ^ c00) := by ring
    have h2 : (N : ℝ) ^ (β - 1) * ((52 : ℝ) ^ (2 / 5 : ℝ) * (N : ℝ) ^ ((9 / 10) * (1 - β)) *
          (Real.log N) ^ c2) * ((c2 + 2) ^ c00 * (Real.log N) ^ c00) =
        (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 *
          ((N : ℝ) ^ (β - 1) * (N : ℝ) ^ ((9 / 10) * (1 - β))) *
            ((Real.log N) ^ c2 * (Real.log N) ^ c00) := by ring
    have h3 : (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 *
          ((N : ℝ) ^ (β - 1) * (N : ℝ) ^ ((9 / 10) * (1 - β))) *
            ((Real.log N) ^ c2 * (Real.log N) ^ c00) =
        (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (N : ℝ) ^ (-(1 - β) / 10) *
          (Real.log N) ^ (c2 + c00) := by rw [hmul, hLcomb]
    have h4 : (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (N : ℝ) ^ (-(1 - β) / 10) *
        (Real.log N) ^ (c2 + c00) ≤
        (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 *
          Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ))) * (Real.log N) ^ (c2 + c00) := by
      have h52 : (0 : ℝ) ≤ (52 : ℝ) ^ (2 / 5 : ℝ) := by positivity
      have hc : (0 : ℝ) ≤ (c2 + 2) ^ c00 := by positivity
      have hLcc : (0 : ℝ) ≤ (Real.log N) ^ (c2 + c00) := Real.rpow_nonneg hL0.le _
      have hthis : (N : ℝ) ^ (-(1 - β) / 10) * (Real.log N) ^ (c2 + c00) ≤
          Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ))) * (Real.log N) ^ (c2 + c00) :=
        mul_le_mul_of_nonneg_right hNdecay hLcc
      have hC : (0 : ℝ) ≤ (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 := mul_nonneg h52 hc
      calc (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (N : ℝ) ^ (-(1 - β) / 10) *
            (Real.log N) ^ (c2 + c00)
          = ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) *
            ((N : ℝ) ^ (-(1 - β) / 10) * (Real.log N) ^ (c2 + c00)) := by ring
        _ ≤ ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) *
            (Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ))) * (Real.log N) ^ (c2 + c00)) :=
            mul_le_mul_of_nonneg_left hthis hC
        _ = (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 *
            Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ))) * (Real.log N) ^ (c2 + c00) := by ring
    have h5 : (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 *
          Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ))) * (Real.log N) ^ (c2 + c00) =
        (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1) *
          ((Real.log N) ^ (c2 + c00 + B + 1) *
            Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ)))) := by
      rw [hid]
      ring
    have h6 : (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1) *
        ((Real.log N) ^ (c2 + c00 + B + 1) *
          Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ)))) ≤
        (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1) := by
      have h52 : (0 : ℝ) ≤ (52 : ℝ) ^ (2 / 5 : ℝ) := by positivity
      have hc : (0 : ℝ) ≤ (c2 + 2) ^ c00 := by positivity
      have hLB : (0 : ℝ) ≤ (Real.log N) ^ (-B - 1) := Real.rpow_nonneg hL0.le _
      have hthis := mul_le_mul_of_nonneg_left hdecay (mul_nonneg (mul_nonneg h52 hc) hLB)
      calc (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1) *
            ((Real.log N) ^ (c2 + c00 + B + 1) *
              Real.exp (-(c0 / 30 * (Real.log N) ^ (1 / 5 : ℝ))))
          ≤ (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1) * 1 := hthis
        _ = (52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1) := by ring
    exact h1.trans (h2.le.trans (h3.le.trans (h4.trans (h5.le.trans h6))))
  calc (N : ℝ) ^ (β - 1) * zeroCountZ β T1 (H269 N A lam) q
      ≤ (N : ℝ) ^ (β - 1) * (K * ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^
          ((12 / 5) * (1 - β)) *
            Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00) :=
        mul_le_mul_of_nonneg_left hcount (Real.rpow_nonneg hN0 _)
    _ = K * ((N : ℝ) ^ (β - 1) * ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^
          ((12 / 5) * (1 - β)) *
            Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00) := by ring
    _ ≤ max K 0 * ((N : ℝ) ^ (β - 1) * ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^
          ((12 / 5) * (1 - β)) *
            Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00) := by
        apply mul_le_mul_of_nonneg_right hKle
        have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (β - 1) := Real.rpow_nonneg hN0 _
        have hX : (0 : ℝ) ≤ ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^
            ((12 / 5) * (1 - β)) := Real.rpow_nonneg (by linarith) _
        positivity
    _ ≤ (max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) + 1) * (Real.log N) ^ (-B - 1) := by
        have h52 : (0 : ℝ) ≤ (52 : ℝ) ^ (2 / 5 : ℝ) := by positivity
        have hc : (0 : ℝ) ≤ (c2 + 2) ^ c00 := by positivity
        have hLB : (0 : ℝ) ≤ (Real.log N) ^ (-B - 1) := Real.rpow_nonneg hL0.le _
        have h1 : max K 0 * ((N : ℝ) ^ (β - 1) *
            ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ ((12 / 5) * (1 - β)) *
              Real.log ((q : ℝ) * (H269 N A lam + |T1| ^ (1 / 3 : ℝ) + 2)) ^ c00) ≤
            max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1)) :=
          mul_le_mul_of_nonneg_left hinner (le_max_right _ _)
        have h2 : max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) * (Real.log N) ^ (-B - 1) ≤
            (max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) + 1) * (Real.log N) ^ (-B - 1) := by
          have h3 : max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) ≤
              max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) + 1 := le_add_of_nonneg_right
                (by norm_num)
          exact mul_le_mul_of_nonneg_right h3 hLB
        have h4 : max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00 * (Real.log N) ^ (-B - 1)) =
            max K 0 * ((52 : ℝ) ^ (2 / 5 : ℝ) * (c2 + 2) ^ c00) * (Real.log N) ^ (-B - 1) := by ring
        exact h1.trans (h4.trans_le h2)

/-- Page 269, the high range of (3.19) from its two parts. PROVED. -/
theorem display319_high_of_parts (c0 : ℝ) (hfree : HighFreePart c0)
    (hdens : HighDensityPart c0) : Display319On (5 / 6) 1 := by
  intro c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨d1, hd1, N1, h1⟩ := hfree c1 c2 B c7 hc1 hc2 hB hc7
  obtain ⟨d2, hd2, K2, N2, h2⟩ := hdens c1 c2 B c7 hc1 hc2 hB hc7
  refine ⟨max d1 d2, lt_of_lt_of_le hd1 (le_max_left _ _), max K2 0,
    max (max N1 N2) (Real.exp 1), ?_⟩
  intro N A α lam a q _ hN hA hAN hcond hq hlam β T1 hβ0 hβ1 hT1
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hL0 : 0 ≤ Real.log N := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hP : 0 ≤ Real.log N ^ (-B - 1) := Real.rpow_nonneg hL0 _
  have hAd : ∀ d, d ≤ max d1 d2 → (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ d ≤ A := by
    intro d hd
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hd)
      (Real.rpow_nonneg hN0 _)).trans hA
  rcases le_or_gt (beta5 c0 N q) β with hb | hb
  · have := h1 N A α lam a q ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
      (hAd d1 (le_max_left _ _)) hAN hcond hq hlam β T1 hb hT1
    rw [this, mul_zero]
    exact mul_nonneg (le_max_right _ _) hP
  · have := h2 N A α lam a q ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
      (hAd d2 (le_max_right _ _)) hAN hcond hq hlam β T1 hβ0 hb hT1
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hP)

/-- The high range through its two parts and the cited Lemmas 4 and 5. -/
theorem display319_high_split : Display319On (5 / 6) 1 := by
  obtain ⟨c0, hc0, hfree⟩ := highFree_of_lemma5 lemma5_cited
  exact display319_high_of_parts c0 hfree (highDensity_of_24 lemma4_eq24_cited c0 hc0)

end

end LeanLab.Zhan1991
