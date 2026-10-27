/-
P0088 Kumchev-Liu, Section 6.2: Corollary 1 from Theorem 3 and Harman-Watt-Wong.

The paper: by Harman, Watt and Wong [9, Theorem 3] there are primes `q₁, q₂` with
`X^{1/2} - X^{0.2625} < qⱼ ≤ X^{1/2} - X^{0.2625}/2`, `qⱼ ≡ j (mod 5)`; then `n - qⱼ²` lies near
`Xⱼ ≈ X^{0.7625}`, `H ≥ Xⱼ^{7/20}`, and Theorem 3 gives (83), (84).

* `HWWPrimes`: the quoted consequence of Harman-Watt-Wong, CITED as a hypothesis.
* `cor1_small`: Corollary 1 for `X^{0.27} ≤ H ≤ X^{3/4}/4`, CONDITIONAL ON Theorem 3 and
  `HWWPrimes`.
* `shortExc_of_small`, with `cnt_add` and `cnt_sum`: a bound for `H ≤ X^d/4` extends to every
  `H ≤ X` by cutting `(X, X + H]` into pieces; the paper does not say this, it applies
  Theorem 3 at `Xⱼ ≈ X^{0.7625}` even when `H > Xⱼ`, outside Theorem 3's range `H ≤ Xⱼ`.
* `cor1_of_thm3`: Corollary 1 as stated, every `X^{0.27} ≤ H ≤ X`, CONDITIONAL ON Theorem 3 and
  `HWWPrimes` only.

AI-written Lean code, Claude, PC run 20261020T0403Z-27388, unit U-1165. Checked only by the
Lean kernel. Binary Goldbach is OPEN; these are Hua type problems.
-/
import LeanLab.KumchevLiu2007.Corollary1A

namespace LeanLab.KumchevLiu2007
open Real

attribute [local instance] Classical.propDecidable

/-- The consequence of Harman, Watt and Wong, Theorem 3, as Kumchev-Liu quote it in Section 6.2:
for large `X` and `j = 1, 2` there is a prime `q ≡ j (mod 5)` with
`X^{1/2} - X^{0.2625} < q ≤ X^{1/2} - X^{0.2625}/2`. CITED. -/
def HWWPrimes : Prop :=
  ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ j : ℕ, (j = 1 ∨ j = 2) → ∃ q : ℕ, q.Prime ∧ q % 5 = j ∧
    X ^ (1 / 2 : ℝ) - X ^ (0.2625 : ℝ) < q ∧ (q : ℝ) ≤ X ^ (1 / 2 : ℝ) - X ^ (0.2625 : ℝ) / 2

/-! ### Real power bookkeeping -/

lemma rp_mul {X a b : ℝ} (hX : 0 < X) : X ^ a * X ^ b = X ^ (a + b) := (rpow_add hX a b).symm

/-- Where `n - q²` lands: if `X^{1/2} - t < q ≤ X^{1/2} - t/2` with `t = X^{0.2625}` and
`X ≥ 2^{112}`, then `X^{0.7625}/2 ≤ X - q² ≤ 2 X^{0.7625}`, and `q > 3`. -/
lemma shift_window {X : ℝ} (hX : (2 : ℝ) ^ (112 : ℕ) ≤ X) {q : ℝ}
    (h1 : X ^ (1 / 2 : ℝ) - X ^ (0.2625 : ℝ) < q) (h2 : q ≤ X ^ (1 / 2 : ℝ) - X ^ (0.2625 : ℝ) / 2) :
    X ^ (0.7625 : ℝ) / 2 ≤ X - q ^ 2 ∧ X - q ^ 2 ≤ 2 * X ^ (0.7625 : ℝ) ∧ 3 < q := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : 0 < X := by linarith
  set s := X ^ (1 / 2 : ℝ) with hs
  set t := X ^ (0.2625 : ℝ) with ht
  have hss : s * s = X := by rw [hs, rp_mul hX0]; norm_num
  have hst : s * t = X ^ (0.7625 : ℝ) := by rw [hs, ht, rp_mul hX0]; norm_num
  have htt : t * t = X ^ (0.525 : ℝ) := by rw [ht, rp_mul hX0]; norm_num
  have ht0 : 0 < t := rpow_pos_of_pos hX0 _
  -- s ≥ 4 t: X^{0.2375} ≥ 4
  have hst4 : 4 * t ≤ s := by
    have e : s = X ^ (0.2375 : ℝ) * t := by rw [hs, ht, rp_mul hX0]; norm_num
    have h4 : (4 : ℝ) ≤ X ^ (0.2375 : ℝ) := by
      have : ((2 : ℝ) ^ (112 : ℕ)) ^ (0.2375 : ℝ) ≤ X ^ (0.2375 : ℝ) :=
        rpow_le_rpow (by positivity) hX (by norm_num)
      have e2 : ((2 : ℝ) ^ (112 : ℕ)) ^ (0.2375 : ℝ) = (2 : ℝ) ^ (26.6 : ℝ) := by
        rw [← rpow_natCast, ← rpow_mul (by norm_num)]; norm_num
      have h26 : (4 : ℝ) ≤ (2 : ℝ) ^ (26.6 : ℝ) := by
        have : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ (26.6 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        norm_num at this ⊢; linarith
      linarith
    rw [e]; nlinarith
  have ht1 : 1 ≤ t := one_le_rpow hX1 (by norm_num)
  have hq0 : 0 ≤ q := by linarith
  refine ⟨?_, ?_, by nlinarith⟩
  · -- q² ≤ (s - t/2)² = X - s t + t²/4
    have hq2 : q ^ 2 ≤ (s - t / 2) ^ 2 := by
      have : 0 ≤ s - t / 2 := by linarith
      nlinarith
    have : t * t ≤ s * t := by nlinarith
    nlinarith
  · have hq2 : (s - t) ^ 2 ≤ q ^ 2 := by
      have : 0 ≤ s - t := by linarith
      nlinarith
    nlinarith

/-- `log Y ≥ (1/2) log X` once `Y ≥ X^{1/2}`. -/
lemma log_half_le {X Y : ℝ} (hX : 0 < X) (hY : X ^ (1 / 2 : ℝ) ≤ Y) : log X / 2 ≤ log Y := by
  have h := log_le_log (rpow_pos_of_pos hX _) hY
  rw [log_rpow hX] at h
  linarith

/-- **Corollary 1 for `X^{0.27} ≤ H ≤ X^{3/4}/4`**, CONDITIONAL ON Theorem 3 and `HWWPrimes`. -/
theorem cor1_small
    (h3 : ShortExcBound (fun n => InH3 n ∧ ¬ IsThreePrimeSquares n) (7 / 20))
    (hw : HWWPrimes) : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
      X ^ (27 / 100 : ℝ) ≤ H → H ≤ X ^ (3 / 4 : ℝ) / 4 →
      (E4Short X H : ℝ) ≤ C * H / Real.log X ^ A := by
  intro A hA
  obtain ⟨C3, X3, hC3⟩ := h3 A hA
  obtain ⟨XW, hXW⟩ := hw
  set C := max C3 0
  refine ⟨2 * C * 2 ^ A, max (max ((2 : ℝ) ^ (112 : ℕ)) XW) ((2 * max X3 1) ^ (2 : ℕ)),
    fun X H hX hH1 hH2 => ?_⟩
  have hXb : (2 : ℝ) ^ (112 : ℕ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXW' : XW ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3' : (2 * max X3 1) ^ (2 : ℕ) ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hXb
  have hX0 : 0 < X := by linarith
  have hH0 : 0 ≤ H := le_trans (rpow_nonneg hX0.le _) hH1
  -- the half power is large
  have hhalf : 2 * max X3 1 ≤ X ^ (1 / 2 : ℝ) := by
    have := rpow_le_rpow (by positivity) hX3' (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← rpow_natCast, ← rpow_mul (by positivity)] at this
    norm_num at this; exact this
  -- one prime at a time
  have key : ∀ j : ℕ, (j = 1 ∨ j = 2) → ∃ q : ℕ, q.Prime ∧ q % 5 = j ∧ 3 < q ∧
      ((q ^ 2 : ℕ) : ℝ) ≤ X ∧ (E3Short (X - (q ^ 2 : ℕ)) H : ℝ) ≤ C * 2 ^ A * H / Real.log X ^ A := by
    intro j hj
    obtain ⟨q, hq, hqj, hq1, hq2⟩ := hXW X hXW' j hj
    obtain ⟨w1, w2, w3⟩ := shift_window hXb hq1 hq2
    have hq3 : 3 < q := by exact_mod_cast w3
    refine ⟨q, hq, hqj, hq3, ?_, ?_⟩
    · push_cast
      have : 0 ≤ X ^ (0.7625 : ℝ) / 2 := by positivity
      linarith
    set Y := X - ((q ^ 2 : ℕ) : ℝ) with hYdef
    have hY1 : X ^ (0.7625 : ℝ) / 2 ≤ Y := by rw [hYdef]; push_cast; exact w1
    have hY2 : Y ≤ 2 * X ^ (0.7625 : ℝ) := by rw [hYdef]; push_cast; exact w2
    -- X^{0.7625}/2 ≥ X^{1/2}
    have hbig : X ^ (1 / 2 : ℝ) ≤ X ^ (0.7625 : ℝ) / 2 := by
      have e : X ^ (0.7625 : ℝ) = X ^ (0.2625 : ℝ) * X ^ (1 / 2 : ℝ) := by rw [rp_mul hX0]; norm_num
      have h2 : (2 : ℝ) ≤ X ^ (0.2625 : ℝ) := by
        have : ((2 : ℝ) ^ (112 : ℕ)) ^ (0.2625 : ℝ) ≤ X ^ (0.2625 : ℝ) :=
          rpow_le_rpow (by positivity) hXb (by norm_num)
        have e2 : ((2 : ℝ) ^ (112 : ℕ)) ^ (0.2625 : ℝ) = (2 : ℝ) ^ (29.4 : ℝ) := by
          rw [← rpow_natCast, ← rpow_mul (by norm_num)]; norm_num
        have : (2 : ℝ) ≤ (2 : ℝ) ^ (29.4 : ℝ) := by
          have := rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) (show (1 : ℝ) ≤ 29.4 by norm_num)
          simpa using this
        linarith
      rw [e]; nlinarith [rpow_nonneg hX0.le (1 / 2 : ℝ)]
    have hYhalf : X ^ (1 / 2 : ℝ) ≤ Y := le_trans hbig hY1
    have hY0 : 0 < Y := lt_of_lt_of_le (rpow_pos_of_pos hX0 _) hYhalf
    have hY3 : X3 ≤ Y := by
      have : X3 ≤ max X3 1 := le_max_left _ _
      have : 0 ≤ max X3 1 := le_trans zero_le_one (le_max_right _ _)
      linarith
    -- H ≥ Y^{7/20}
    have hHY : Y ^ (7 / 20 : ℝ) ≤ H := by
      have a1 : Y ^ (7 / 20 : ℝ) ≤ (2 * X ^ (0.7625 : ℝ)) ^ (7 / 20 : ℝ) :=
        rpow_le_rpow hY0.le hY2 (by norm_num)
      have a2 : (2 * X ^ (0.7625 : ℝ)) ^ (7 / 20 : ℝ) = 2 ^ (7 / 20 : ℝ) * X ^ (0.266875 : ℝ) := by
        rw [mul_rpow (by norm_num) (rpow_nonneg hX0.le _), ← rpow_mul hX0.le]; norm_num
      have a3 : 2 ^ (7 / 20 : ℝ) * X ^ (0.266875 : ℝ) ≤ X ^ (27 / 100 : ℝ) := by
        have e : X ^ (27 / 100 : ℝ) = X ^ (0.003125 : ℝ) * X ^ (0.266875 : ℝ) := by
          rw [rp_mul hX0]; norm_num
        have h2 : (2 : ℝ) ^ (7 / 20 : ℝ) ≤ X ^ (0.003125 : ℝ) := by
          have : ((2 : ℝ) ^ (112 : ℕ)) ^ (0.003125 : ℝ) ≤ X ^ (0.003125 : ℝ) :=
            rpow_le_rpow (by positivity) hXb (by norm_num)
          have e2 : ((2 : ℝ) ^ (112 : ℕ)) ^ (0.003125 : ℝ) = (2 : ℝ) ^ (7 / 20 : ℝ) := by
            rw [← rpow_natCast, ← rpow_mul (by norm_num)]; norm_num
          linarith
        rw [e]; nlinarith [rpow_nonneg hX0.le (0.266875 : ℝ)]
      linarith
    -- H ≤ Y
    have hHY2 : H ≤ Y := by
      have : X ^ (3 / 4 : ℝ) ≤ X ^ (0.7625 : ℝ) := rpow_le_rpow_of_exponent_le hX1 (by norm_num)
      linarith
    have hb := hC3 Y H hY3 hHY hHY2
    -- log Y ≥ log X / 2
    have hlog := log_half_le hX0 hYhalf
    have hlX : 0 < log X := log_pos (by linarith)
    have hlXA : 0 < (log X / 2) ^ A := rpow_pos_of_pos (by linarith) _
    have hlYA : (log X / 2) ^ A ≤ log Y ^ A := rpow_le_rpow (by linarith) hlog hA.le
    have e2 : (log X / 2) ^ A = log X ^ A / 2 ^ A := by
      rw [div_rpow hlX.le (by norm_num)]
    have hC0 : 0 ≤ C := le_max_right _ _
    calc (E3Short Y H : ℝ) ≤ C3 * H / log Y ^ A := hb
      _ ≤ C * H / log Y ^ A := by
          apply div_le_div_of_nonneg_right _ (le_trans hlXA.le hlYA)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hH0
      _ ≤ C * H / (log X / 2) ^ A := div_le_div_of_nonneg_left (by positivity) hlXA hlYA
      _ = C * 2 ^ A * H / log X ^ A := by
          rw [e2]; field_simp
  obtain ⟨q₁, hq₁, h₁, h₁3, hX₁, b₁⟩ := key 1 (Or.inl rfl)
  obtain ⟨q₂, hq₂, h₂, h₂3, hX₂, b₂⟩ := key 2 (Or.inr rfl)
  have hE := E4_le_two_E3 hq₁ hq₂ h₁ h₂ h₁3 h₂3 hH0 hX₁ hX₂
  have hE' : (E4Short X H : ℝ) ≤ (E3Short (X - (q₁ ^ 2 : ℕ)) H : ℝ) + E3Short (X - (q₂ ^ 2 : ℕ)) H := by
    exact_mod_cast hE
  calc (E4Short X H : ℝ) ≤ C * 2 ^ A * H / log X ^ A + C * 2 ^ A * H / log X ^ A := by linarith
    _ = 2 * C * 2 ^ A * H / log X ^ A := by ring


/-! ### Cutting a long window into short ones -/

/-- `cnt` over `(X, X + a + b]` is at most `cnt` over `(X, X + a]` plus over `(X + a, X + a + b]`. -/
theorem cnt_add (S : ℕ → Prop) {X a b : ℝ} (hX : 0 ≤ X) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cntIoc S X (a + b) ≤ cntIoc S X a + cntIoc S (X + a) b := by
  unfold cntIoc
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  rw [mem_cnt] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  have hfl : (n : ℝ) ≤ X + (a + b) := le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))
  rw [Finset.mem_union, mem_cnt, mem_cnt]
  by_cases hc : (n : ℝ) ≤ X + a
  · left; exact ⟨Nat.le_floor hc, h2, h3⟩
  · right
    push Not at hc
    exact ⟨Nat.le_floor (by linarith), hc, h3⟩

lemma cnt_zero (S : ℕ → Prop) {X : ℝ} (hX : 0 ≤ X) : cntIoc S X 0 = 0 := by
  unfold cntIoc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn h
  rw [Finset.mem_range, add_zero] at hn
  have : (n : ℝ) ≤ X := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp hn) (Nat.floor_le hX)
  linarith [h.1]

/-- `cnt` over `(X, X + kℓ]` is at most the sum over the `k` pieces `(X + iℓ, X + (i + 1)ℓ]`. -/
theorem cnt_sum (S : ℕ → Prop) {X ℓ : ℝ} (hX : 0 ≤ X) (hℓ : 0 ≤ ℓ) (k : ℕ) :
    cntIoc S X (k * ℓ) ≤ ∑ i ∈ Finset.range k, cntIoc S (X + i * ℓ) ℓ := by
  induction k with
  | zero => simp [cnt_zero S hX]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e : ((k + 1 : ℕ) : ℝ) * ℓ = k * ℓ + ℓ := by push_cast; ring
    rw [e]
    have := cnt_add S hX (by positivity : (0 : ℝ) ≤ k * ℓ) hℓ
    omega

/-- **From short windows to all windows**: a bound for `X^c ≤ H ≤ X^d/4` gives `ShortExcBound`,
every `X^c ≤ H ≤ X`, by cutting `(X, X + H]` into pieces of length between `X^d/8` and `X^d/4`. -/
theorem shortExc_of_small (S : ℕ → Prop) {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hc1 : c ≤ 1)
    (h : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ X H : ℝ, X0 ≤ X → X ^ c ≤ H → H ≤ X ^ d / 4 →
      (cntIoc S X H : ℝ) ≤ C * H / Real.log X ^ A) : ShortExcBound S c := by
  intro A hA
  obtain ⟨C, X0, hC⟩ := h A hA
  set C' := max C 0
  refine ⟨C', max (max X0 3) ((16 : ℝ) ^ (1 / (d - c))), fun X H hX hH1 hH2 => ?_⟩
  have hX0' : X0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX16 : (16 : ℝ) ^ (1 / (d - c)) ≤ X := le_trans (le_max_right _ _) hX
  have hXp : 0 < X := by linarith
  have hlX : 0 < log X := log_pos (by linarith)
  have hLA : 0 < log X ^ A := rpow_pos_of_pos hlX _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hH0 : 0 ≤ H := le_trans (rpow_nonneg hXp.le _) hH1
  -- the gap X^{d-c} ≥ 16
  have hgap : (16 : ℝ) ≤ X ^ (d - c) := by
    have := rpow_le_rpow (by positivity) hX16 (by linarith : (0 : ℝ) ≤ d - c)
    rw [← rpow_mul (by norm_num), one_div_mul_cancel (by linarith), rpow_one] at this
    exact this
  have hdc : X ^ d = X ^ (d - c) * X ^ c := by rw [← rpow_add hXp]; ring_nf
  set M := X ^ d / 4 with hM
  have hcpos : 0 < X ^ c := rpow_pos_of_pos hXp _
  have hMpos : 0 < M := by rw [hM]; positivity
  by_cases hsmall : H ≤ M
  · calc (cntIoc S X H : ℝ) ≤ C * H / log X ^ A := hC X H hX0' hH1 hsmall
      _ ≤ C' * H / log X ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hH0) hLA.le
  push Not at hsmall
  set k := ⌈H / M⌉₊ with hk
  have hHM : 1 < H / M := by rw [lt_div_iff₀ hMpos]; linarith
  have hk1 : (1 : ℝ) ≤ k := by
    have := Nat.le_ceil (H / M); rw [← hk] at this; linarith
  have hkpos : (0 : ℝ) < k := by linarith
  have hkle : (k : ℝ) < H / M + 1 := by rw [hk]; exact Nat.ceil_lt_add_one (by positivity)
  set ℓ := H / k with hℓ
  have hℓM : ℓ ≤ M := by
    rw [hℓ, div_le_iff₀ hkpos]
    have := Nat.le_ceil (H / M); rw [← hk] at this
    rw [div_le_iff₀ hMpos] at this; linarith
  have hℓM2 : M / 2 ≤ ℓ := by
    rw [hℓ, le_div_iff₀ hkpos]
    have : (k : ℝ) < 2 * (H / M) := by linarith
    have h2 : M * k < M * (2 * (H / M)) := mul_lt_mul_of_pos_left this hMpos
    rw [show M * (2 * (H / M)) = 2 * H by field_simp] at h2
    linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hkℓ : (k : ℝ) * ℓ = H := by rw [hℓ]; field_simp
  have hsplit := cnt_sum S hXp.le hℓ0 k
  rw [hkℓ] at hsplit
  have hpiece : ∀ i ∈ Finset.range k, (cntIoc S (X + i * ℓ) ℓ : ℝ) ≤ C' * ℓ / log X ^ A := by
    intro i hi
    rw [Finset.mem_range] at hi
    set Y := X + i * ℓ
    have hY1 : X ≤ Y := by have : 0 ≤ (i : ℝ) * ℓ := by positivity
                           linarith
    have hY2 : Y ≤ 2 * X := by
      have : (i : ℝ) * ℓ ≤ k * ℓ := mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hℓ0
      linarith
    have hYp : 0 < Y := by linarith
    -- Y^c ≤ ℓ
    have hYc : Y ^ c ≤ ℓ := by
      have a1 : Y ^ c ≤ (2 * X) ^ c := rpow_le_rpow hYp.le hY2 hc.le
      have a2 : (2 * X) ^ c = 2 ^ c * X ^ c := mul_rpow (by norm_num) hXp.le
      have a3 : (2 : ℝ) ^ c ≤ 2 := by
        have := rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hc1
        simpa using this
      have a4 : 2 * X ^ c ≤ M / 2 := by
        rw [hM, hdc]; nlinarith
      have : 2 ^ c * X ^ c ≤ 2 * X ^ c := mul_le_mul_of_nonneg_right a3 hcpos.le
      linarith
    have hYd : ℓ ≤ Y ^ d / 4 := by
      have : X ^ d ≤ Y ^ d := rpow_le_rpow hXp.le hY1 (by linarith)
      rw [hM] at hℓM; linarith
    have hb := hC Y ℓ (le_trans hX0' hY1) hYc hYd
    have hlY : log X ≤ log Y := log_le_log hXp hY1
    have hLYA : log X ^ A ≤ log Y ^ A := rpow_le_rpow hlX.le hlY hA.le
    calc (cntIoc S Y ℓ : ℝ) ≤ C * ℓ / log Y ^ A := hb
      _ ≤ C' * ℓ / log Y ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hℓ0)
            (le_trans hLA.le hLYA)
      _ ≤ C' * ℓ / log X ^ A := div_le_div_of_nonneg_left (by positivity) hLA hLYA
  calc (cntIoc S X H : ℝ) ≤ ((∑ i ∈ Finset.range k, cntIoc S (X + i * ℓ) ℓ : ℕ) : ℝ) := by
        exact_mod_cast hsplit
    _ = ∑ i ∈ Finset.range k, (cntIoc S (X + i * ℓ) ℓ : ℝ) := by push_cast; rfl
    _ ≤ ∑ i ∈ Finset.range k, C' * ℓ / log X ^ A := Finset.sum_le_sum hpiece
    _ = k * (C' * ℓ / log X ^ A) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = C' * H / log X ^ A := by rw [← hkℓ]; ring

/-- **Kumchev-Liu Corollary 1**, every `X^{0.27} ≤ H ≤ X`: CONDITIONAL ON Theorem 3 and the
Harman-Watt-Wong primes only. -/
theorem cor1_of_thm3
    (h3 : ShortExcBound (fun n => InH3 n ∧ ¬ IsThreePrimeSquares n) (7 / 20))
    (hw : HWWPrimes) : ShortExcBound (fun n => InH4 n ∧ ¬ IsFourPrimeSquares n) (27 / 100) :=
  shortExc_of_small _ (by norm_num) (by norm_num : (27 / 100 : ℝ) < 3 / 4) (by norm_num)
    (cor1_small h3 hw)

#print axioms cnt_add
#print axioms cnt_sum
#print axioms shortExc_of_small
#print axioms cor1_of_thm3

#print axioms shift_window
#print axioms cor1_small

end LeanLab.KumchevLiu2007
