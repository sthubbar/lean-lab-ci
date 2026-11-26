/-
P0076 J. Teräväinen, arXiv 1611.08585, Lemma 5.2, page 18, quoting Matomäki and Shao,
Vinogradov's three primes theorem with almost twin primes, Lemma 7.4.
The leaves `lemma52_dyad` and `lemma52_half` of `WeightedPrimeSplit` are proved here from one
general lemma for any order convex range `R N ⊆ range N`, from the single new leaf
`twisted_interval_bound`, the Fourier dual count of a short exponential sum over an interval.
The class indicator of `𝒬 (mod Q)` is expanded in additive characters, the premise on `𝒬`
bounds every nonzero frequency, and the Fourier complexity of `χ` reduces the twisted sums
`∑ χ(t - n) e(a n / Q)` to linear exponential sums over the interval.
AI wrote this Lean code, Claude, session CLOUD-S69, burst-20261122. Checked only by the Lean
kernel. The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.WeightedPrimeSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-! ### The character `eC` -/

private theorem eC_add1122b (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

private theorem eC_norm1122b (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

private theorem eC_conj1122b (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem eC_nat_mul1122b (k : ℕ) (x : ℝ) : eC ((k : ℝ) * x) = (eC x) ^ k := by
  unfold eC; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

private theorem eC_int1122b (m : ℤ) : eC (m : ℝ) = 1 := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  exact ⟨m, by push_cast; ring⟩

private theorem eC_eq_one_iff1122b (x : ℝ) : eC x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (2 * Real.pi * Complex.I) * (x : ℂ) = (2 * Real.pi * Complex.I) * (n : ℂ) := by
      rw [hn]; ring
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := mul_left_cancel₀ hne h
    exact_mod_cast this
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/-! ### Orthogonality of additive characters modulo `Q` -/

/-- `∑_{a mod Q} e(a m / Q) = Q 1_{Q ∣ m}`. -/
theorem orth1122b (Q : ℕ) (hQ : 1 ≤ Q) (m : ℤ) :
    ∑ a ∈ range Q, eC ((a : ℝ) * m / Q) = if (Q : ℤ) ∣ m then (Q : ℂ) else 0 := by
  have hQ' : (Q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Q := by exact_mod_cast hQ
    exact this.ne'
  have hterm : ∀ a : ℕ, eC ((a : ℝ) * m / Q) = eC ((m : ℝ) / Q) ^ a := by
    intro a; rw [← eC_nat_mul1122b]; congr 1; ring
  simp_rw [hterm]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have : eC ((Q : ℝ) * (j : ℝ) / Q) = 1 := by
      rw [show (Q : ℝ) * (j : ℝ) / Q = (j : ℝ) by field_simp]
      exact eC_int1122b j
    push_cast
    simp [this]
  · have hne : eC ((m : ℝ) / Q) ≠ 1 := by
      rw [Ne, eC_eq_one_iff1122b]; rintro ⟨j, hj⟩
      apply h; refine ⟨j, ?_⟩
      have : (m : ℝ) = Q * j := by
        rw [div_eq_iff hQ'] at hj; linarith
      exact_mod_cast this
    rw [geom_sum_eq hne, ← eC_nat_mul1122b,
      show (Q : ℝ) * ((m : ℝ) / Q) = (m : ℝ) by field_simp, eC_int1122b]
    simp

theorem dvd_iff_mod1122b (Q n c : ℕ) (hc : c < Q) : (Q : ℤ) ∣ (n : ℤ) - c ↔ n % Q = c := by
  rw [← Int.modEq_iff_dvd, Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod,
    Nat.mod_eq_of_lt hc]
  constructor <;> intro h <;> omega

/-! ### Helpers for the dual count -/

private theorem eC_re1122b (t : ℝ) : (eC t).re = Real.cos (2 * Real.pi * t) := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re]

private theorem eC_im1122b (t : ℝ) : (eC t).im = Real.sin (2 * Real.pi * t) := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_im]

/-- `‖1 - e(t)‖ = 2 |sin π t|`. -/
private theorem norm_one_sub_eC1122b (t : ℝ) : ‖1 - eC t‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hsq : ‖1 - eC t‖ ^ 2 = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : (1 - eC t).re = 1 - Real.cos (2 * Real.pi * t) := by
      simp [eC_re1122b]
    have h2 : (1 - eC t).im = -Real.sin (2 * Real.pi * t) := by
      simp [eC_im1122b]
    rw [h1, h2]
    have hc := Real.cos_two_mul' (Real.pi * t)
    have hs := Real.sin_two_mul (Real.pi * t)
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * t)
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring]
    have hsq1 : (2 * |Real.sin (Real.pi * t)|) ^ 2 = 4 * Real.sin (Real.pi * t) ^ 2 := by
      rw [mul_pow, sq_abs]; norm_num
    have h1c : 1 - Real.cos (2 * (Real.pi * t)) = 2 * Real.sin (Real.pi * t) ^ 2 := by
      linarith [hc, hsc]
    rw [h1c, hsq1, hs]
    nlinarith [hsc]
  have h1 : 0 ≤ ‖1 - eC t‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin (Real.pi * t)| := by positivity
  nlinarith [hsq, h1, h2]

/-- For an integer `m` within `1/2` of `γ`, `2 |γ - m| ≤ |sin π γ|`. -/
private theorem two_mul_abs_sub_int_le_sin1122b {γ : ℝ} (m : ℤ)
    (hm : |γ - (m : ℝ)| ≤ 1 / 2) : 2 * |γ - (m : ℝ)| ≤ |Real.sin (Real.pi * γ)| := by
  set s : ℝ := γ - (m : ℝ) with hs
  have hγ : γ = (m : ℝ) + s := by rw [hs]; ring
  have hsin : Real.sin (Real.pi * γ) = (-1 : ℝ) ^ m * Real.sin (Real.pi * s) := by
    rw [hγ, show Real.pi * ((m : ℝ) + s) = Real.pi * s + (m : ℝ) * Real.pi by ring,
      Real.sin_add_int_mul_pi]
  have hx0 : 0 ≤ Real.pi * |s| := by positivity
  have hx1 : Real.pi * |s| ≤ Real.pi / 2 := by
    have h := abs_nonneg s
    nlinarith [Real.pi_pos, hm, h]
  have hmul := Real.mul_le_sin hx0 hx1
  have heq : 2 / Real.pi * (Real.pi * |s|) = 2 * |s| := by
    field_simp
  have hslo : -(1 / 2) ≤ s := (abs_le.mp hm).1
  have hshi : s ≤ 1 / 2 := (abs_le.mp hm).2
  have hsinabs : Real.sin (Real.pi * |s|) = |Real.sin (Real.pi * s)| := by
    rcases le_total 0 s with h | h
    · have hp : 0 ≤ Real.sin (Real.pi * s) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos, hshi])
      rw [abs_of_nonneg h, abs_of_nonneg hp]
    · have hp : Real.sin (Real.pi * s) ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le (by nlinarith [Real.pi_pos, h])
          (by nlinarith [Real.pi_pos, hslo])
      rw [abs_of_nonpos h, mul_neg, Real.sin_neg, abs_of_nonpos hp]
  rw [hsin, abs_mul]
  have h1 : |((-1 : ℝ) ^ m)| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [h1, one_mul, ← hsinabs]
  linarith [hmul, heq.le, heq.ge]

/-- `‖Σ_{n < J} e(n x)‖ ≤ 1 / |sin π x|`. -/
private theorem norm_dirichlet1122b {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (J : ℕ) :
    ‖∑ k ∈ range J, eC ((k : ℝ) * x)‖ ≤ 1 / |Real.sin (Real.pi * x)| := by
  have hne_norm : ‖(1 : ℂ) - eC x‖ = 2 * |Real.sin (Real.pi * x)| := norm_one_sub_eC1122b x
  have hpos : 0 < 2 * |Real.sin (Real.pi * x)| := by
    have : |Real.sin (Real.pi * x)| ≠ 0 := abs_ne_zero.mpr hx
    positivity
  have hne : (1 : ℂ) - eC x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hne_norm
    linarith
  have h1e : eC x ≠ 1 := by
    intro h0
    exact hne (by rw [h0, sub_self])
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ range J) => eC_nat_mul1122b k x)]
  rw [geom_sum_eq h1e]
  have hden : ‖eC x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
    rw [← norm_neg, neg_sub, hne_norm]
  rw [norm_div, hden]
  have hnum : ‖(eC x) ^ J - 1‖ ≤ 2 := by
    calc ‖(eC x) ^ J - 1‖ ≤ ‖(eC x) ^ J‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, eC_norm1122b, norm_one]; norm_num
  calc ‖(eC x) ^ J - 1‖ / (2 * |Real.sin (Real.pi * x)|)
      ≤ 2 / (2 * |Real.sin (Real.pi * x)|) :=
        div_le_div_of_nonneg_right hnum hpos.le
    _ = 1 / |Real.sin (Real.pi * x)| := by field_simp

/-- The geometric sum bound over an order convex range of `ℕ`: for an integer `m` within `1/2`
of `γ`, `‖Σ_{n ∈ S} e(γ n)‖ · 2 |γ - m| ≤ 1`. -/
private theorem geom_interval1122b (S : Finset ℕ)
    (hconv : ∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S)
    (γ : ℝ) (m : ℤ) (hm : |γ - (m : ℝ)| ≤ 1 / 2) :
    ‖∑ n ∈ S, eC (γ * n)‖ * (2 * |γ - (m : ℝ)|) ≤ 1 := by
  set δ : ℝ := |γ - (m : ℝ)| with hδ
  have hδ0 : 0 ≤ δ := abs_nonneg _
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set p := S.min' hne with hp
  set q := S.max' hne with hq
  have hpq : p ≤ q := Finset.min'_le S q (Finset.max'_mem S hne)
  have hSeq : S = Finset.Icc p q := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro n hn
      exact Finset.mem_Icc.2 ⟨Finset.min'_le S n hn, Finset.le_max' S n hn⟩
    · intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
      exact hconv _ (Finset.min'_mem S hne) _ (Finset.max'_mem S hne) n h1 h2
  have hstep : ‖∑ n ∈ S, eC (γ * n)‖
      ≤ ‖∑ i ∈ range (q + 1 - p), (eC γ) ^ i‖ := by
    rw [hSeq, show Finset.Icc p q = Finset.Ico p (q + 1) by
      ext n; simp, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i : ℕ, eC (γ * ((p + i : ℕ) : ℝ)) =
        eC (γ * (p : ℝ)) * (eC γ) ^ i := by
      intro i
      rw [show γ * ((p + i : ℕ) : ℝ) = γ * (p : ℝ) + (i : ℝ) * γ by
        push_cast; ring, eC_add1122b, eC_nat_mul1122b]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ range (q + 1 - p)) => hterm i),
      ← Finset.mul_sum, norm_mul, eC_norm1122b, one_mul]
  rcases eq_or_lt_of_le hδ0 with h0 | hpos
  · rw [← h0, mul_zero]; norm_num
  have hsin : 2 * δ ≤ |Real.sin (Real.pi * γ)| := by
    rw [hδ]; exact two_mul_abs_sub_int_le_sin1122b m hm
  have hne1 : eC γ ≠ 1 := by
    intro h
    rw [eC_eq_one_iff1122b] at h
    obtain ⟨j, hj⟩ := h
    have hcast : ((j - m : ℤ) : ℝ) = γ - (m : ℝ) := by
      push_cast [hj]; ring
    have habs : |((j - m : ℤ) : ℝ)| ≤ 1 / 2 := by rw [hcast]; exact hm
    have hlt : ((|j - m| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs]; linarith
    have hle0 : |j - m| ≤ 0 := by
      have h1 : |j - m| < (1 : ℤ) := by exact_mod_cast hlt
      omega
    have h2 : j - m = 0 := abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _))
    have hjm : j = m := by omega
    have hγm : γ = (m : ℝ) := by rw [hj, hjm]
    rw [hγm, sub_self, abs_zero] at hδ
    linarith [hδ]
  have hnum : ‖(eC γ) ^ (q + 1 - p) - 1‖ ≤ 2 := by
    calc ‖(eC γ) ^ (q + 1 - p) - 1‖
        ≤ ‖(eC γ) ^ (q + 1 - p)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, eC_norm1122b, norm_one]; norm_num
  have hden : ‖eC γ - 1‖ = 2 * |Real.sin (Real.pi * γ)| := by
    rw [← norm_neg, neg_sub, norm_one_sub_eC1122b]
  have hdenpos : 0 < ‖eC γ - 1‖ := by
    rw [hden]; have := hpos; nlinarith [Real.pi_pos]
  have hgeom : ‖∑ i ∈ range (q + 1 - p), (eC γ) ^ i‖
      ≤ 2 / (2 * |Real.sin (Real.pi * γ)|) := by
    rw [geom_sum_eq hne1, norm_div, hden]
    exact div_le_div_of_nonneg_right hnum (by rw [hden] at hdenpos; linarith)
  have hfin : 2 / (2 * |Real.sin (Real.pi * γ)|) ≤ 1 / (2 * δ) := by
    have hs : 0 < 2 * δ := by linarith
    have hsp : 0 < 2 * |Real.sin (Real.pi * γ)| := by linarith [hsin, hpos]
    rw [div_le_div_iff₀ hsp hs]
    nlinarith [hsin]
  have h2 : 1 / (2 * δ) * (2 * δ) = 1 := by field_simp
  calc ‖∑ n ∈ S, eC (γ * n)‖ * (2 * δ) ≤ (1 / (2 * δ)) * (2 * δ) := by
        apply mul_le_mul_of_nonneg_right (hstep.trans (hgeom.trans hfin)) (by linarith)
    _ = 1 := h2

/-- Integers with pairwise distances at most `L` number at most `L + 1`. -/
private theorem card_le_of_diam1122b (s : Finset ℕ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x ∈ s, ∀ z ∈ s, |(x : ℝ) - (z : ℝ)| ≤ L) :
    (s.card : ℝ) ≤ L + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [card_empty, Nat.cast_zero]
    linarith
  have hpq : s.min' hne ≤ s.max' hne := Finset.min'_le s (s.max' hne) (Finset.max'_mem s hne)
  have hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) := by
    intro n hn
    exact Finset.mem_Icc.2 ⟨Finset.min'_le s n hn, Finset.le_max' s n hn⟩
  have h1 : s.card ≤ s.max' hne + 1 - s.min' hne := by
    calc s.card ≤ (Finset.Icc (s.min' hne) (s.max' hne)).card := Finset.card_le_card hsub
      _ = s.max' hne + 1 - s.min' hne := Nat.card_Icc _ _
  have h2 : ((s.max' hne + 1 - s.min' hne : ℕ) : ℝ)
      = (s.max' hne : ℝ) + 1 - (s.min' hne : ℝ) := by
    rw [Nat.cast_sub (by omega : s.min' hne ≤ s.max' hne + 1)]
    push_cast
    ring
  have h3 : |(s.max' hne : ℝ) - (s.min' hne : ℝ)| ≤ L :=
    h _ (Finset.max'_mem s hne) _ (Finset.min'_mem s hne)
  have h4 : (s.max' hne : ℝ) - (s.min' hne : ℝ) ≤ L := (abs_le.mp h3).2
  calc (s.card : ℝ) ≤ ((s.max' hne + 1 - s.min' hne : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (s.max' hne : ℝ) + 1 - (s.min' hne : ℝ) := h2
    _ ≤ L + 1 := by linarith

/-- The `Q` frequencies `a/Q - β`, `a < Q`, are spaced `1/Q` apart: at most `6 t Q + 3` of them
lie within `t` of an integer, for `0 < t ≤ 1/2`. -/
private theorem count_dual1122b (Q : ℕ) (hQ : 1 ≤ Q) (β : ℝ) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1 / 2) :
    (((Finset.range Q).filter (fun a : ℕ => ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t)).card : ℝ)
      ≤ 6 * t * Q + 3 := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  set ξ : ℝ := (Q : ℝ) * β with hξ
  set k₀ : ℤ := ⌊ξ / Q⌋ with hk₀
  set y : ℝ := ξ - (k₀ : ℝ) * Q with hy
  have hy0 : 0 ≤ y := by
    have h := Int.floor_le (ξ / Q)
    rw [hy]
    have : (⌊ξ / Q⌋ : ℝ) * Q ≤ (ξ / Q) * Q := by
      exact mul_le_mul_of_nonneg_right h (le_of_lt hQpos)
    rw [div_mul_cancel₀ ξ (ne_of_gt hQpos)] at this
    linarith
  have hy1 : y < Q := by
    have h := Int.lt_floor_add_one (ξ / Q)
    rw [hy]
    have h2 : (ξ / Q) * Q < ((⌊ξ / Q⌋ : ℝ) + 1) * Q := by
      exact mul_lt_mul_of_pos_right h hQpos
    rw [div_mul_cancel₀ ξ (ne_of_gt hQpos)] at h2
    linarith
  set A₁ : Finset ℕ := (Finset.range Q).filter (fun a : ℕ => |(a : ℝ) - y| ≤ t * Q) with hA₁
  set A₂ : Finset ℕ :=
    (Finset.range Q).filter (fun a : ℕ => |(a : ℝ) - (y + Q)| ≤ t * Q) with hA₂
  set A₃ : Finset ℕ :=
    (Finset.range Q).filter (fun a : ℕ => |(a : ℝ) - (y - Q)| ≤ t * Q) with hA₃
  have hsub : (Finset.range Q).filter
      (fun a : ℕ => ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t) ⊆ A₁ ∪ (A₂ ∪ A₃) := by
    intro a ha
    obtain ⟨haQ, k, hk⟩ := Finset.mem_filter.mp ha
    have hltQ : a < Q := by simpa using haQ
    have haQ' : (a : ℝ) < (Q : ℝ) := by exact_mod_cast hltQ
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have h1 : |(a : ℝ) - ξ - (k : ℝ) * Q| ≤ t * Q := by
      have hmul : ((a : ℝ) / Q - β - (k : ℝ)) * Q = (a : ℝ) - ξ - (k : ℝ) * Q := by
        rw [hξ]
        field_simp
      rw [← hmul, abs_mul, abs_of_pos hQpos]
      exact mul_le_mul_of_nonneg_right hk (le_of_lt hQpos)
    set K : ℤ := k + k₀ with hK
    have h2 : |(a : ℝ) - y - (K : ℝ) * Q| ≤ t * Q := by
      have heq : (a : ℝ) - y - (K : ℝ) * Q = (a : ℝ) - ξ - (k : ℝ) * Q := by
        have hKr : (K : ℝ) = (k : ℝ) + (k₀ : ℝ) := by
          rw [hK]; push_cast; ring
        rw [hKr, hy]
        ring
      rw [heq]; exact h1
    have htQ : t * Q ≤ (Q : ℝ) / 2 := by nlinarith [ht1]
    have hlow := (abs_le.mp h2).1
    have hupp := (abs_le.mp h2).2
    have hKlo : -(Q : ℝ) - (Q : ℝ) / 2 ≤ (K : ℝ) * Q := by
      nlinarith [hupp, htQ, hy1, ha0]
    have hle1 : (a : ℝ) + 1 ≤ (Q : ℝ) := by
      exact_mod_cast (show a + 1 ≤ Q by omega)
    have hKhi : (K : ℝ) * Q ≤ (Q : ℝ) - 1 + (Q : ℝ) / 2 := by
      nlinarith [hlow, htQ, hy0, hle1]
    have hKge : (-1 : ℤ) ≤ K := by
      by_contra hcon
      have hKle : K ≤ -2 := by omega
      have hKr : (K : ℝ) ≤ -2 := by exact_mod_cast hKle
      nlinarith [hKlo, hKr, hQpos, hQ1]
    have hKle1 : K ≤ 1 := by
      by_contra hcon
      have hKge2 : (2 : ℤ) ≤ K := by omega
      have hKr : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKge2
      nlinarith [hKhi, hKr, hQpos, hQ1]
    have hm₁ : a ∈ A₁ ∨ a ∈ A₂ ∨ a ∈ A₃ := by
      interval_cases K
      · right; right
        refine Finset.mem_filter.mpr ⟨haQ, ?_⟩
        have hKr : ((-1 : ℤ) : ℝ) = -1 := by push_cast; ring
        have heq : (a : ℝ) - (y - Q) = (a : ℝ) - y - ((-1 : ℤ) : ℝ) * Q := by
          rw [hKr]; ring
        rw [heq]; exact h2
      · left
        refine Finset.mem_filter.mpr ⟨haQ, ?_⟩
        have hKr : ((0 : ℤ) : ℝ) = 0 := by push_cast; ring
        have heq : (a : ℝ) - y = (a : ℝ) - y - ((0 : ℤ) : ℝ) * Q := by
          rw [hKr]; ring
        rw [heq]; exact h2
      · right; left
        refine Finset.mem_filter.mpr ⟨haQ, ?_⟩
        have hKr : ((1 : ℤ) : ℝ) = 1 := by push_cast; ring
        have heq : (a : ℝ) - (y + Q) = (a : ℝ) - y - ((1 : ℤ) : ℝ) * Q := by
          rw [hKr]; ring
        rw [heq]; exact h2
    rcases hm₁ with h' | h' | h'
    · exact Finset.mem_union_left _ h'
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h')
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ h')
  have hdiam : ∀ (c : ℝ), ((Finset.range Q).filter (fun a : ℕ => |(a : ℝ) - c| ≤ t * Q)).card
      ≤ 2 * t * Q + 1 := by
    intro c
    exact card_le_of_diam1122b _ (by positivity) (by
      intro x hx z hz
      have hx' : |(x : ℝ) - c| ≤ t * Q := (Finset.mem_filter.mp hx).2
      have hz' : |(z : ℝ) - c| ≤ t * Q := (Finset.mem_filter.mp hz).2
      have h4 : |(x : ℝ) - (z : ℝ)| ≤ |(x : ℝ) - c| + |c - (z : ℝ)| := abs_sub_le _ _ _
      have h5 : |c - (z : ℝ)| = |(z : ℝ) - c| := abs_sub_comm _ _
      rw [h5] at h4
      linarith)
  have hA₁ : (A₁.card : ℝ) ≤ 2 * t * Q + 1 := hdiam y
  have hA₂ : (A₂.card : ℝ) ≤ 2 * t * Q + 1 := hdiam (y + Q)
  have hA₃ : (A₃.card : ℝ) ≤ 2 * t * Q + 1 := hdiam (y - Q)
  have hstep1 : (((Finset.range Q).filter (fun a : ℕ => ∃ k : ℤ,
      |(a : ℝ) / Q - β - (k : ℝ)| ≤ t)).card : ℝ) ≤ ((A₁ ∪ (A₂ ∪ A₃)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hstep2 : ((A₁ ∪ (A₂ ∪ A₃)).card : ℝ) ≤ (A₁.card : ℝ) + ((A₂ ∪ A₃).card : ℝ) := by
    exact_mod_cast Finset.card_union_le A₁ (A₂ ∪ A₃)
  have hstep3 : ((A₂ ∪ A₃).card : ℝ) ≤ (A₂.card : ℝ) + (A₃.card : ℝ) := by
    exact_mod_cast Finset.card_union_le A₂ A₃
  linarith

/-! ### The new leaf -/

/-- LEAF: the Fourier dual count of a linear exponential sum over an interval, the step of
Matomäki and Shao Lemma 7.4 behind the error `Q C² √N` of Lemma 5.2, page 18. Class MEDIUM.
For an interval `S` of length at most `N`, `|∑_{n ∈ S} e(γ n)| ≤ min(|S|, 1/(2‖γ‖))`, and
summing over the `Q` frequencies `a/Q - β` gives at most `2N + Q (1 + log Q)`, which is at most
`K (N + Q √N)` once `6 Q² ≤ N`. -/
theorem twisted_interval_bound : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
    ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
      K * (N + Q * Real.sqrt N) := by
  refine ⟨100, by norm_num, ?_⟩
  intro N Q hQ hNQ S hsub hconv β
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hN6 : 6 ≤ N := by
    have h1 : 6 * 1 ≤ 6 * Q ^ 2 := by
      have : 1 ≤ Q ^ 2 := by nlinarith
      nlinarith
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set M : ℝ := Real.sqrt N with hMdef
  have hMM : M * M = (N : ℝ) := by
    rw [hMdef]; exact Real.mul_self_sqrt (le_of_lt hNpos)
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Real.sqrt_pos.mpr hNpos
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    have : (2 : ℝ) ^ 2 ≤ (N : ℝ) := by
      have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 4 ≤ N)
      nlinarith
    exact Real.le_sqrt_of_sq_le this
  set t₀ : ℝ := 1 / (2 * M) with ht₀
  have ht₀pos : 0 < t₀ := by rw [ht₀]; positivity
  have ht₀half : t₀ ≤ 1 / 2 := by
    rw [ht₀, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have ht₀M : t₀ * M = 1 / 2 := by
    rw [ht₀]; field_simp
  set X : ℕ → ℝ := fun a => (a : ℝ) / Q - β with hX
  set Δ : ℕ → ℝ := fun a => |X a - (round (X a) : ℝ)| with hΔ
  have hΔle : ∀ a, Δ a ≤ 1 / 2 := fun a => abs_sub_round (X a)
  -- the cardinality of the frequencies near an integer
  have hcard : ((range Q).filter (fun a : ℕ => Δ a ≤ t₀)).card ≤ 6 * t₀ * Q + 3 := by
    have heq : (range Q).filter (fun a : ℕ => Δ a ≤ t₀)
        = (range Q).filter (fun a : ℕ => ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t₀) := by
      refine Finset.filter_congr fun a _ => ?_
      constructor
      · intro h
        exact ⟨round (X a), h⟩
      · rintro ⟨k, hk⟩
        exact le_trans (round_le (X a) k) hk
    rw [heq]
    exact count_dual1122b Q hQ β ht₀pos ht₀half
  -- the pointwise bound
  have hpt : ∀ a : ℕ, ‖∑ n ∈ S, eC (X a * n)‖ ≤ if Δ a ≤ t₀ then (N : ℝ) else M := by
    intro a
    by_cases h : Δ a ≤ t₀
    · rw [if_pos h]
      have h1 : ‖∑ n ∈ S, eC (X a * n)‖ ≤ (S.card : ℝ) := by
        calc ‖∑ n ∈ S, eC (X a * n)‖ ≤ ∑ n ∈ S, ‖eC (X a * n)‖ := norm_sum_le _ _
          _ = (S.card : ℝ) := by simp [eC_norm1122b]
      have h2 : (S.card : ℝ) ≤ (N : ℝ) := by
        have h3 : S.card ≤ N := by
          calc S.card ≤ (range N).card := Finset.card_le_card hsub
            _ = N := Finset.card_range N
        exact_mod_cast h3
      linarith
    · rw [if_neg h]
      have hlt : t₀ < Δ a := not_le.mp h
      have hpos : 0 < Δ a := lt_trans ht₀pos hlt
      have hg := geom_interval1122b S hconv (X a) (round (X a)) (hΔle a)
      have h2δ : 0 < 2 * Δ a := by linarith
      have hb : ‖∑ n ∈ S, eC (X a * n)‖ ≤ 1 / (2 * Δ a) := by
        rw [le_div_iff₀ h2δ]
        linarith [hg]
      have hfin : 1 / (2 * Δ a) ≤ 1 / (2 * t₀) := by
        apply one_div_le_one_div_of_le (by linarith)
        linarith
      have hMeq : 1 / (2 * t₀) = M := by
        rw [ht₀]; field_simp
      linarith [hb, hfin, hMeq.le, hMeq.ge]
  -- the split by the threshold
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range Q)
    (fun a : ℕ => Δ a ≤ t₀) (fun a : ℕ => ‖∑ n ∈ S, eC (X a * n)‖)
  have hpart1 : ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀),
      ‖∑ n ∈ S, eC (X a * n)‖ ≤ (6 * t₀ * Q + 3) * N := by
    have h1 : ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀),
        ‖∑ n ∈ S, eC (X a * n)‖
        ≤ ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀), (N : ℝ) := by
      refine Finset.sum_le_sum fun a ha => ?_
      have hh := hpt a
      rwa [if_pos (Finset.mem_filter.mp ha).2] at hh
    have h2 : ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀), (N : ℝ)
        = (((range Q).filter (fun a : ℕ => Δ a ≤ t₀)).card : ℝ) * N := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (((range Q).filter (fun a : ℕ => Δ a ≤ t₀)).card : ℝ) ≤ 6 * t₀ * Q + 3 := by
      exact_mod_cast hcard
    have hNnn : (0 : ℝ) ≤ N := le_of_lt hNpos
    calc ∑ a ∈ (range Q).filter (fun a : ℕ => Δ a ≤ t₀), ‖∑ n ∈ S, eC (X a * n)‖
        ≤ (((range Q).filter (fun a : ℕ => Δ a ≤ t₀)).card : ℝ) * N := by rw [← h2]; exact h1
      _ ≤ (6 * t₀ * Q + 3) * N := by
          apply mul_le_mul_of_nonneg_right h3 hNnn
  have hpart2 : ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀),
      ‖∑ n ∈ S, eC (X a * n)‖ ≤ (Q : ℝ) * M := by
    have h1 : ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀),
        ‖∑ n ∈ S, eC (X a * n)‖
        ≤ ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀), M := by
      refine Finset.sum_le_sum fun a ha => ?_
      have hh := hpt a
      rwa [if_neg (Finset.mem_filter.mp ha).2] at hh
    have h2 : ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀), M
        = (((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card : ℝ) * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : ((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card ≤ Q := by
      calc ((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card ≤ (range Q).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = Q := Finset.card_range Q
    have h3' : (((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast h3
    have hMnn : (0 : ℝ) ≤ M := le_of_lt hMpos
    calc ∑ a ∈ (range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀), ‖∑ n ∈ S, eC (X a * n)‖
        ≤ (((range Q).filter (fun a : ℕ => ¬ Δ a ≤ t₀)).card : ℝ) * M := by
          rw [← h2]; exact h1
      _ ≤ (Q : ℝ) * M := by
          apply mul_le_mul_of_nonneg_right h3' hMnn
  have htotal : ∑ a ∈ range Q, ‖∑ n ∈ S, eC (X a * n)‖ ≤ (6 * t₀ * Q + 3) * N + Q * M := by
    rw [← hsplit]
    linarith [hpart1, hpart2]
  have hkey : 6 * t₀ * (Q : ℝ) * N = 3 * (Q : ℝ) * M := by
    have hNeq : (N : ℝ) = M * M := hMM.symm
    have h1 : t₀ * M = 1 / 2 := ht₀M
    rw [hNeq]
    -- 6 * t₀ * Q * (M * M) = 3 * Q * M
    have : 6 * t₀ * (Q : ℝ) * (M * M) = 3 * (Q : ℝ) * M * (2 * (t₀ * M)) := by ring
    rw [this, h1]
    ring
  have hfin1 : (6 * t₀ * (Q : ℝ) + 3) * (N : ℝ) + (Q : ℝ) * M
      = 4 * ((Q : ℝ) * M) + 3 * (N : ℝ) := by
    calc (6 * t₀ * (Q : ℝ) + 3) * (N : ℝ) + (Q : ℝ) * M
        = 6 * t₀ * (Q : ℝ) * (N : ℝ) + 3 * (N : ℝ) + (Q : ℝ) * M := by ring
      _ = 3 * ((Q : ℝ) * M) + 3 * (N : ℝ) + (Q : ℝ) * M := by rw [hkey]; ring
      _ = 4 * ((Q : ℝ) * M) + 3 * (N : ℝ) := by ring
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := le_of_lt hQpos
  have hMnn : (0 : ℝ) ≤ M := le_of_lt hMpos
  calc ∑ a ∈ range Q, ‖∑ n ∈ S, eC (X a * ↑n)‖
      ≤ 4 * ((Q : ℝ) * M) + 3 * (N : ℝ) := htotal.trans (le_of_eq hfin1)
    _ ≤ 100 * ((N : ℝ) + (Q : ℝ) * Real.sqrt N) := by
        rw [show Real.sqrt N = M from hMdef.symm]
        nlinarith [hQnn, hMnn, hNpos.le]

/-! ### The coefficient bound from the premise on `𝒬` -/

theorem coef_bound1122b (Q : ℕ) (𝒬 : Finset ℕ) (η₀ : ℝ)
    (hexp : ∀ q a : ℕ, q ∣ Q → q ≠ 1 → 0 < a → a.Coprime q →
        ‖∑ c₀ ∈ 𝒬, eC ((a : ℝ) * c₀ / q)‖ ≤ η₀ * #𝒬)
    (a : ℕ) (ha0 : 0 < a) (haQ : a < Q) :
    ‖∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q))‖ ≤ η₀ * #𝒬 := by
  set g := Nat.gcd a Q with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ ha0
  have hga : g ∣ a := Nat.gcd_dvd_left a Q
  have hgQ : g ∣ Q := Nat.gcd_dvd_right a Q
  have hcop : (a / g).Coprime (Q / g) := Nat.coprime_div_gcd_div_gcd hgpos
  have hqdvd : Q / g ∣ Q := Nat.div_dvd_of_dvd hgQ
  have hapos : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha0 hga) hgpos
  have hq1 : Q / g ≠ 1 := by
    intro h1
    have hQg : Q = g := by
      have := Nat.mul_div_cancel' hgQ
      rw [h1, mul_one] at this; exact this.symm
    have : g ≤ a := Nat.le_of_dvd ha0 hga
    omega
  have hbound := hexp (Q / g) (a / g) hqdvd hq1 hapos hcop
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hQpos : 0 < Q := by omega
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hconv : ∀ c : ℕ, ((a / g : ℕ) : ℝ) * c / ((Q / g : ℕ) : ℝ) = (a : ℝ) * c / Q := by
    intro c
    rw [Nat.cast_div hga hgR, Nat.cast_div hgQ hgR]
    field_simp
  simp_rw [hconv] at hbound
  have hc : ∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q)) =
      (starRingEnd ℂ) (∑ c ∈ 𝒬, eC ((a : ℝ) * c / Q)) := by
    rw [map_sum]; simp_rw [eC_conj1122b]
  rw [hc, Complex.norm_conj]
  exact hbound

/-! ### The general lemma -/

/-- Lemma 5.2, page 18, on any order convex range `R N ⊆ range N`, from the leaf
`twisted_interval_bound`. -/
theorem lemma52On_of_twisted (R : ℕ → Finset ℕ) (hsub : ∀ N, R N ⊆ range N)
    (hconv : ∀ N, ∀ x ∈ R N, ∀ z ∈ R N, ∀ y, x ≤ y → y ≤ z → y ∈ R N)
    (htw : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
      ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
      ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
        K * (N + Q * Real.sqrt N)) :
    Lemma52On R := by
  obtain ⟨K, hK, hKb⟩ := htw
  refine ⟨2 * K, by positivity, ?_⟩
  intro Cc χ hχ0 hχC N Q hQ hNQ 𝒬 h𝒬 hne η₀ hη₀ hexp t
  obtain ⟨cf, α, hcf, hχ⟩ := hχC
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQR : (Q : ℝ) ≠ 0 := hQpos.ne'
  have h𝒬pos : (0 : ℝ) < #𝒬 := by exact_mod_cast hne.card_pos
  set S := R N with hS
  set f : ℕ → ℝ := fun n => χ (t - n) with hf
  -- the twisted sums
  set T : ℕ → ℂ := fun a => ∑ n ∈ S, (f n : ℂ) * eC ((a : ℝ) * n / Q) with hT
  set G : Fin Cc → ℕ → ℂ := fun k a => ∑ n ∈ S, eC (((a : ℝ) / Q - α k) * n) with hG
  have hTexp : ∀ a, T a = ∑ k, cf k * eC (α k * t) * G k a := by
    intro a
    simp only [hT, hG, hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hχ (t - n), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, mul_assoc, ← eC_add1122b, ← eC_add1122b]
    congr 2
    push_cast
    ring
  have hTnorm : ∀ a, ‖T a‖ ≤ ∑ k, (Cc : ℝ) * ‖G k a‖ := by
    intro a
    rw [hTexp a]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, eC_norm1122b, mul_one]
    exact mul_le_mul_of_nonneg_right (hcf k) (norm_nonneg _)
  have hTsum : ∑ a ∈ range Q, ‖T a‖ ≤ (Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N))) := by
    calc ∑ a ∈ range Q, ‖T a‖ ≤ ∑ a ∈ range Q, ∑ k, (Cc : ℝ) * ‖G k a‖ :=
          Finset.sum_le_sum fun a _ => hTnorm a
      _ = (Cc : ℝ) * ∑ k, ∑ a ∈ range Q, ‖G k a‖ := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
      _ ≤ (Cc : ℝ) * ∑ _k : Fin Cc, K * (N + Q * Real.sqrt N) := by
          gcongr with k
          exact hKb N Q hQ hNQ S (hsub N) (hconv N) (α k)
      _ = (Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the expansion of the class indicator
  set coef : ℕ → ℂ := fun a => ∑ c ∈ 𝒬, eC (-((a : ℝ) * c / Q)) with hcoef
  set F : ℝ := ∑ c₀ ∈ 𝒬, ∑ n ∈ S.filter (fun n => n % Q = c₀), f n with hF
  have hexpand : ((Q : ℝ) * F : ℂ) = ∑ a ∈ range Q, coef a * T a := by
    have h1 : F = ∑ n ∈ S, ∑ c ∈ 𝒬, if n % Q = c then f n else 0 := by
      rw [hF]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    have h2 : ∑ a ∈ range Q, coef a * T a =
        ∑ a ∈ range Q, ∑ n ∈ S, ∑ c ∈ 𝒬,
          (f n : ℂ) * eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) := by
      simp only [hcoef, hT, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun n _ =>
        Finset.sum_congr rfl fun c _ => ?_
      have hadd := eC_add1122b ((a : ℝ) * n / Q) (-((a : ℝ) * c / Q))
      rw [show ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) = (a : ℝ) * n / Q + -((a : ℝ) * c / Q) by
        push_cast; ring, hadd]
      ring
    have h3 : ∑ a ∈ range Q, ∑ n ∈ S, ∑ c ∈ 𝒬,
          (f n : ℂ) * eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) =
        ∑ n ∈ S, ∑ c ∈ 𝒬, (f n : ℂ) *
          ∑ a ∈ range Q, eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) := by
      simp_rw [Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
    have h4 : ∀ n ∈ S, ∀ c ∈ 𝒬, (f n : ℂ) *
          ∑ a ∈ range Q, eC ((a : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) / Q) =
        (f n : ℂ) * (if n % Q = c then (Q : ℂ) else 0) := by
      intro n _ c hc
      have hcQ : c < Q := Finset.mem_range.1 (h𝒬 hc)
      rw [orth1122b Q hQ]
      by_cases h : n % Q = c
      · rw [if_pos ((dvd_iff_mod1122b Q n c hcQ).2 h), if_pos h]
      · rw [if_neg (mt (dvd_iff_mod1122b Q n c hcQ).1 h), if_neg h]
    rw [h2, h3, h1, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [h4 n hn c hc]
    split_ifs <;> simp; ring
  -- the frequency `a = 0`
  have h0 : coef 0 * T 0 = (((#𝒬 : ℝ) * ∑ n ∈ S, f n : ℝ) : ℂ) := by
    simp [hcoef, hT, eC]
  have hQmem : 0 ∈ range Q := Finset.mem_range.2 (by omega)
  have hre : (Q : ℝ) * F = (#𝒬 : ℝ) * (∑ n ∈ S, f n) +
      (∑ a ∈ (range Q).erase 0, coef a * T a).re := by
    have := congrArg Complex.re hexpand
    have hcast : ((Q : ℝ) : ℂ) * (F : ℂ) = (((Q : ℝ) * F : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.ofReal_re, ← Finset.add_sum_erase _ _ hQmem, Complex.add_re, h0,
      Complex.ofReal_re] at this
    exact this
  have hrest : -(η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖) ≤
      (∑ a ∈ (range Q).erase 0, coef a * T a).re := by
    have hn : ‖∑ a ∈ (range Q).erase 0, coef a * T a‖ ≤ η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖ := by
      calc ‖∑ a ∈ (range Q).erase 0, coef a * T a‖
          ≤ ∑ a ∈ (range Q).erase 0, ‖coef a * T a‖ := norm_sum_le _ _
        _ ≤ ∑ a ∈ (range Q).erase 0, η₀ * #𝒬 * ‖T a‖ := by
            refine Finset.sum_le_sum fun a ha => ?_
            rw [norm_mul]
            have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
            have haQ : a < Q := Finset.mem_range.1 (Finset.mem_of_mem_erase ha)
            exact mul_le_mul_of_nonneg_right
              (coef_bound1122b Q 𝒬 η₀ hexp a (Nat.pos_of_ne_zero ha0) haQ) (norm_nonneg _)
        _ = η₀ * #𝒬 * ∑ a ∈ (range Q).erase 0, ‖T a‖ := by rw [Finset.mul_sum]
        _ ≤ η₀ * #𝒬 * ∑ a ∈ range Q, ‖T a‖ := by
            gcongr
            exact Finset.erase_subset _ _
    have := Complex.abs_re_le_norm (∑ a ∈ (range Q).erase 0, coef a * T a)
    have := neg_abs_le (∑ a ∈ (range Q).erase 0, coef a * T a).re
    linarith
  -- arithmetic
  have hNR : ((6 * Q ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNQ
  push_cast at hNR
  have hQs : (Q : ℝ) * Real.sqrt N ≤ N := by
    have hq : (Q : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
    calc (Q : ℝ) * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hstep : η₀ * ∑ a ∈ range Q, ‖T a‖ ≤ 2 * K * (η₀ * (Cc : ℝ) ^ 2 * N) := by
    calc η₀ * ∑ a ∈ range Q, ‖T a‖ ≤ η₀ * ((Cc : ℝ) * (Cc * (K * (N + Q * Real.sqrt N)))) :=
          mul_le_mul_of_nonneg_left hTsum hη₀.le
      _ ≤ η₀ * ((Cc : ℝ) * (Cc * (K * (N + N)))) := by gcongr
      _ = 2 * K * (η₀ * (Cc : ℝ) ^ 2 * N) := by ring
  have hextra : 0 ≤ 2 * K * ((Q : ℝ) * (Cc : ℝ) ^ 2 * Real.sqrt N) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ h𝒬pos]
  nlinarith [mul_le_mul_of_nonneg_left hstep h𝒬pos.le, mul_nonneg h𝒬pos.le hextra]

/-! ### The two ranges are order convex -/

theorem dyad_convex1122b (N : ℕ) :
    ∀ x ∈ dyad N, ∀ z ∈ dyad N, ∀ y, x ≤ y → y ≤ z → y ∈ dyad N := by
  intro x hx z hz y hxy hyz
  simp only [dyad, Finset.mem_filter, Finset.mem_range] at hx hz ⊢
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hyz' : (y : ℝ) ≤ z := by exact_mod_cast hyz
  exact ⟨by omega, by linarith [hx.2.1], by linarith [hz.2.2]⟩

theorem half_convex1122b (N : ℕ) :
    ∀ x ∈ half N, ∀ z ∈ half N, ∀ y, x ≤ y → y ≤ z → y ∈ half N := by
  intro x hx z hz y hxy hyz
  simp only [half, Finset.mem_filter, Finset.mem_range] at hx hz ⊢
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hyz' : (y : ℝ) ≤ z := by exact_mod_cast hyz
  exact ⟨by omega, by linarith [hx.2.1], by linarith [hz.2.2]⟩

/-! ### The assemblies -/

/-- `lemma52_dyad` from the leaf `twisted_interval_bound`. -/
theorem lemma52_dyad_of_leaves : Lemma52On dyad :=
  lemma52On_of_twisted dyad (fun _ => Finset.filter_subset _ _) dyad_convex1122b
    twisted_interval_bound

/-- `lemma52_half` from the leaf `twisted_interval_bound`. -/
theorem lemma52_half_of_leaves : Lemma52On half :=
  lemma52On_of_twisted half (fun _ => Finset.filter_subset _ _) half_convex1122b
    twisted_interval_bound

theorem lemma52_dyad_twin : type_of% @LeanLab.Teravainen2016.lemma52_dyad :=
  lemma52_dyad_of_leaves

theorem lemma52_half_twin : type_of% @LeanLab.Teravainen2016.lemma52_half :=
  lemma52_half_of_leaves

end LeanLab.Teravainen2016
