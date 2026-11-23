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

/-- LEAF: Page 269, "by Lemma 5": above `beta5` the count is `0`. MEDIUM. Apply Lemma 5 at height
`N`, where `q ≤ L^{c₂}`; the window `[T₁, T₁ + H]` lies in `|t| ≤ N` by `T269_bound` and
`H269_bounds`; then `zeroCountZ_eq_zero_of_free` of SPLIT_theorem3_p2_1122. -/
theorem highFree_of_lemma5 (h5 : Lemma5NoExc) : ∃ c0 : ℝ, 0 < c0 ∧ HighFreePart c0 := by
  sorry

/-- LEAF: Page 269, "by (2.4)": the density part for every `c₀ > 0`. MEDIUM. Enlarge the window to
`H' = H + |T₁|^{1/3} + 2` with `zeroCountZ_mono_H_proof`, apply (2.4), use `H' ≪ N^{3/8} L^{c₁}`
from `H269_bounds` and `T269_bound`, so `q^{12/5} H'^{12/5} N⁻¹ ≤ N^{-1/20}` for large `N`, and
`1 - β > c₀/(2 L^{4/5})` below `beta5`. -/
theorem highDensity_of_24 (h24 : Lemma4Eq24) (c0 : ℝ) (hc0 : 0 < c0) : HighDensityPart c0 := by
  sorry

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
