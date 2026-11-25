/-
Helpers for `leaf_lfm_fourth_power` in SPLIT_leaf_long_fourth_moment.
P0069 page 24, ||L||_4^4 << L^B qT for L <= qT, from Lemma 9.
Route: write the long polynomial as an interval sum over Ioc a b, apply
`Reflection425.interval_fourth_moment_of_lemma9` at the auxiliary height x' = (c2 + 1) x^2,
bound the polar sum by `Reflection425.principal_polar_fourth_sum_le` and the size of the
well spaced set by `wellSpaced_card_le_real`. CONDITIONAL ON Lemma 9 as hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_small_L_338
import LeanLab.BakerHarmanPintz1997.WellSpaced

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- The long polynomial is the interval polynomial over `Ioc a b'`, with
`a = ⌊c1 F⌋₊` and `b' = max a (⌈c2 F⌉₊ - 1)`. -/
theorem lfm_longDP_eq_Ioc (c1 c2 F : ℝ) :
    longDP c1 c2 F = ⟨fun _ => 1, Ioc ⌊c1 * F⌋₊ (max ⌊c1 * F⌋₊ (⌈c2 * F⌉₊ - 1))⟩ := by
  unfold longDP
  congr 1
  ext n
  simp only [mem_Ioo, mem_Ioc]
  omega

/-- The right end `b'` of the interval is at most `c2 qT` when `F <= qT`. -/
theorem lfm_right_end_le (c1 c2 F Y : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) (hY : 0 ≤ Y)
    (hF : F ≤ Y) :
    ((max ⌊c1 * F⌋₊ (⌈c2 * F⌉₊ - 1) : ℕ) : ℝ) ≤ c2 * Y := by
  have hc2p : 0 < c2 := hc1.trans hc2
  by_cases h0 : 0 ≤ F
  · have hle : max ⌊c1 * F⌋₊ (⌈c2 * F⌉₊ - 1) ≤ ⌊c2 * F⌋₊ := by
      apply max_le
      · exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hc2.le h0)
      · have := Nat.ceil_le_floor_add_one (c2 * F)
        omega
    calc ((max ⌊c1 * F⌋₊ (⌈c2 * F⌉₊ - 1) : ℕ) : ℝ) ≤ (⌊c2 * F⌋₊ : ℝ) := by exact_mod_cast hle
      _ ≤ c2 * F := Nat.floor_le (by positivity)
      _ ≤ c2 * Y := mul_le_mul_of_nonneg_left hF hc2p.le
  · push Not at h0
    have ha : ⌊c1 * F⌋₊ = 0 := Nat.floor_of_nonpos (by nlinarith)
    have hb : ⌈c2 * F⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by nlinarith)
    rw [ha, hb]
    simp only [zero_tsub, max_self, Nat.cast_zero]
    positivity

/-- The fourth power bound for one configuration, with explicit constants.
CONDITIONAL ON Lemma 9 through the hypothesis `h9i`, the interval form of Lemma 9. -/
theorem lfm_fourth_power_core (B9 K9 : ℝ)
    (h9i : ∀ x : ℝ, 2 ≤ x → ∀ a b : ℕ, a ≤ b → (b : ℝ) ≤ x →
      ∀ c : Cfg, c.WellSpaced → 1 ≤ c.q → (c.q : ℝ) ≤ x → 2 ≤ c.T → c.T ≤ x →
        pnorm ⟨fun _ => 1, Ioc a b⟩ c 4 ^ 4 ≤
          K9 * (c.q * c.T * L x ^ B9 +
            L x ^ 4 * c.S.card * (c.q ^ 2 / c.T ^ 2 + (b : ℝ) ^ 2 / c.T ^ 4) +
            (b : ℝ) ^ 2 * ∑ e ∈ c.S, delta e.2 / (1 + |e.1|) ^ 4))
    (A0 c1 c2 F x : ℝ) (hc1 : 0 < c1) (hc2 : c1 < c2) (c : Cfg)
    (hx : max (c2 + 1) (Real.exp 1) ≤ x)
    (hstd : c.Std x) (hqA : (c.q : ℝ) ≤ L x ^ A0)
    (hheight : ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1|)
    (hF : F ≤ (c.q : ℝ) * c.T) :
    pnorm (longDP c1 c2 F) c 4 ^ 4 ≤
      (|K9| * (3 ^ |B9| + 243 * (1 + c2 ^ 2) + 48 * c2 ^ 2)) *
        (L x ^ (|B9| + 4 + 2 * |A0|) * (c.q * c.T)) := by
  obtain ⟨hws, hq1, hqx, hT2, hTx⟩ := hstd
  have hc2p : 0 < c2 := hc1.trans hc2
  have hxc : c2 + 1 ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hx0 : 0 < x := by linarith
  set q : ℝ := (c.q : ℝ) with hqdef
  set T : ℝ := c.T with hTdef
  have hq1' : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq1
  have hq0 : 0 < q := by linarith
  have hT0 : 0 < T := by linarith
  have hqT : 0 ≤ q * T := by positivity
  -- the auxiliary height
  set x' : ℝ := (c2 + 1) * x ^ 2 with hx'
  have hxx' : x ≤ x' := by
    have : x ≤ x ^ 2 := by nlinarith
    nlinarith
  have hx'pos : 0 < x' := by positivity
  set ℓ : ℝ := L x with hℓ
  set ℓ' : ℝ := L x' with hℓ'
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, L]
    exact (Real.le_log_iff_exp_le hx0).mpr hxe
  have hℓ0 : 0 < ℓ := by linarith
  have hℓℓ' : ℓ ≤ ℓ' := Real.log_le_log hx0 hxx'
  have hℓ'1 : 1 ≤ ℓ' := hℓ1.trans hℓℓ'
  have hℓ'3 : ℓ' ≤ 3 * ℓ := by
    rw [hℓ', hℓ, L, L, hx', Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have := Real.log_le_log (by linarith) hxc
    push_cast
    linarith
  -- the interval
  set a : ℕ := ⌊c1 * F⌋₊ with ha
  set b : ℕ := max ⌊c1 * F⌋₊ (⌈c2 * F⌉₊ - 1) with hb
  have hab : a ≤ b := le_max_left _ _
  have hbY : (b : ℝ) ≤ c2 * (q * T) := lfm_right_end_le c1 c2 F (q * T) hc1 hc2 hqT hF
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hqx' : q ≤ x' := hqx.trans hxx'
  have hTx' : T ≤ x' := by linarith
  have hbx' : (b : ℝ) ≤ x' := by
    have h1 : q * T ≤ x * x := mul_le_mul hqx (by linarith) hT0.le hx0.le
    calc (b : ℝ) ≤ c2 * (q * T) := hbY
      _ ≤ c2 * (x * x) := mul_le_mul_of_nonneg_left h1 hc2p.le
      _ ≤ x' := by rw [hx']; nlinarith
  have hmain := h9i x' (by linarith) a b hab hbx' c hws hq1 hqx' hT2.le hTx'
  rw [lfm_longDP_eq_Ioc]
  -- the polar sum and the size of S
  have hpolar := Reflection425.principal_polar_fourth_sum_le c hT0 hheight
  have hS : (c.S.card : ℝ) ≤ q * (2 * T + 1) :=
    wellSpaced_card_le_real c hT0.le (by omega) hws
  set Sc : ℝ := (c.S.card : ℝ) with hSc
  set Sd : ℝ := ∑ e ∈ c.S, delta e.2 / (1 + |e.1|) ^ 4 with hSddef
  have hSc0 : 0 ≤ Sc := Nat.cast_nonneg _
  have hS3 : Sc ≤ 3 * (q * T) := by nlinarith
  -- powers of the logarithm
  set P : ℝ := ℓ ^ (|B9| + 4 + 2 * |A0|) with hP
  have hP0 : 0 ≤ P := by positivity
  have hpow_mono : ∀ u v : ℝ, u ≤ v → ℓ ^ u ≤ ℓ ^ v := fun u v huv =>
    Real.rpow_le_rpow_of_exponent_le hℓ1 huv
  have hQ : q ^ 2 ≤ ℓ ^ (2 * |A0|) := by
    have h1 : q ≤ ℓ ^ |A0| := hqA.trans (hpow_mono _ _ (le_abs_self A0))
    calc q ^ 2 ≤ (ℓ ^ |A0|) ^ 2 := pow_le_pow_left₀ hq0.le h1 2
      _ = ℓ ^ (2 * |A0|) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]
        ring_nf
  have hQP : q ^ 2 ≤ P := hQ.trans (hpow_mono _ _ (by linarith [abs_nonneg B9]))
  have hℓ4Q : ℓ ^ 4 * q ^ 2 ≤ P := by
    calc ℓ ^ 4 * q ^ 2 ≤ ℓ ^ 4 * ℓ ^ (2 * |A0|) :=
          mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = ℓ ^ ((4 : ℝ) + 2 * |A0|) := by
          rw [Real.rpow_add hℓ0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ ≤ P := hpow_mono _ _ (by linarith [abs_nonneg B9])
  have hB : ℓ' ^ B9 ≤ 3 ^ |B9| * P := by
    calc ℓ' ^ B9 ≤ ℓ' ^ |B9| := Real.rpow_le_rpow_of_exponent_le hℓ'1 (le_abs_self B9)
      _ ≤ (3 * ℓ) ^ |B9| := Real.rpow_le_rpow (by linarith) hℓ'3 (abs_nonneg _)
      _ = 3 ^ |B9| * ℓ ^ |B9| := Real.mul_rpow (by norm_num) hℓ0.le
      _ ≤ 3 ^ |B9| * P := mul_le_mul_of_nonneg_left
          (hpow_mono _ _ (by linarith [abs_nonneg A0])) (by positivity)
  have hℓ'4 : ℓ' ^ 4 ≤ 81 * ℓ ^ 4 := by
    calc ℓ' ^ 4 ≤ (3 * ℓ) ^ 4 := pow_le_pow_left₀ (by linarith) hℓ'3 4
      _ = 81 * ℓ ^ 4 := by ring
  -- the three terms
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT2' : (1 : ℝ) ≤ T ^ 2 := one_le_pow₀ hT1
  have hb2 : (b : ℝ) ^ 2 ≤ c2 ^ 2 * q ^ 2 * T ^ 2 := by
    calc (b : ℝ) ^ 2 ≤ (c2 * (q * T)) ^ 2 := pow_le_pow_left₀ hb0 hbY 2
      _ = c2 ^ 2 * q ^ 2 * T ^ 2 := by ring
  have hfrac : q ^ 2 / T ^ 2 + (b : ℝ) ^ 2 / T ^ 4 ≤ (1 + c2 ^ 2) * q ^ 2 := by
    have h1 : q ^ 2 / T ^ 2 ≤ q ^ 2 := div_le_self (by positivity) hT2'
    have h2 : (b : ℝ) ^ 2 / T ^ 4 ≤ c2 ^ 2 * q ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      calc (b : ℝ) ^ 2 ≤ c2 ^ 2 * q ^ 2 * T ^ 2 := hb2
        _ ≤ c2 ^ 2 * q ^ 2 * T ^ 2 * T ^ 2 := le_mul_of_one_le_right (by positivity) hT2'
        _ = c2 ^ 2 * q ^ 2 * T ^ 4 := by ring
    linarith
  have ht2 : ℓ' ^ 4 * Sc * (q ^ 2 / T ^ 2 + (b : ℝ) ^ 2 / T ^ 4) ≤
      243 * (1 + c2 ^ 2) * P * (q * T) := by
    calc ℓ' ^ 4 * Sc * (q ^ 2 / T ^ 2 + (b : ℝ) ^ 2 / T ^ 4)
        ≤ (81 * ℓ ^ 4) * (3 * (q * T)) * ((1 + c2 ^ 2) * q ^ 2) := by
          gcongr
      _ = 243 * (1 + c2 ^ 2) * (ℓ ^ 4 * q ^ 2) * (q * T) := by ring
      _ ≤ 243 * (1 + c2 ^ 2) * P * (q * T) := by gcongr
  have ht3 : (b : ℝ) ^ 2 * Sd ≤ 48 * c2 ^ 2 * P * (q * T) := by
    have hSd0 : 0 ≤ Sd := by
      apply sum_nonneg
      intro e _
      unfold delta
      split_ifs <;> positivity
    calc (b : ℝ) ^ 2 * Sd ≤ (c2 ^ 2 * q ^ 2 * T ^ 2) * (16 * Sc / T ^ 4) :=
          mul_le_mul hb2 hpolar hSd0 (by positivity)
      _ ≤ (c2 ^ 2 * q ^ 2 * T ^ 2) * (16 * (3 * (q * T)) / T ^ 4) := by gcongr
      _ = 48 * c2 ^ 2 * q ^ 2 * (q * T) / T ^ 2 := by field_simp; ring
      _ ≤ 48 * c2 ^ 2 * q ^ 2 * (q * T) := div_le_self (by positivity) hT2'
      _ ≤ 48 * c2 ^ 2 * P * (q * T) := by gcongr
  have ht1 : q * T * ℓ' ^ B9 ≤ 3 ^ |B9| * P * (q * T) := by
    calc q * T * ℓ' ^ B9 ≤ q * T * (3 ^ |B9| * P) := mul_le_mul_of_nonneg_left hB hqT
      _ = _ := by ring
  have hR0 : 0 ≤ q * T * ℓ' ^ B9 + ℓ' ^ 4 * Sc * (q ^ 2 / T ^ 2 + (b : ℝ) ^ 2 / T ^ 4) +
      (b : ℝ) ^ 2 * Sd := by
    have hSd0 : 0 ≤ Sd := by
      apply sum_nonneg
      intro e _
      unfold delta
      split_ifs <;> positivity
    positivity
  calc _ ≤ K9 * (q * T * ℓ' ^ B9 + ℓ' ^ 4 * Sc * (q ^ 2 / T ^ 2 + (b : ℝ) ^ 2 / T ^ 4) +
        (b : ℝ) ^ 2 * Sd) := hmain
    _ ≤ |K9| * (q * T * ℓ' ^ B9 + ℓ' ^ 4 * Sc * (q ^ 2 / T ^ 2 + (b : ℝ) ^ 2 / T ^ 4) +
        (b : ℝ) ^ 2 * Sd) := mul_le_mul_of_nonneg_right (le_abs_self K9) hR0
    _ ≤ |K9| * (3 ^ |B9| * P * (q * T) + 243 * (1 + c2 ^ 2) * P * (q * T) +
        48 * c2 ^ 2 * P * (q * T)) := by
      gcongr
    _ = (|K9| * (3 ^ |B9| + 243 * (1 + c2 ^ 2) + 48 * c2 ^ 2)) * (P * (q * T)) := by ring

#print axioms lfm_longDP_eq_Ioc
#print axioms lfm_right_end_le
#print axioms lfm_fourth_power_core

end LeanLab.BakerHarmanPintz1997
