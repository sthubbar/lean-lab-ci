/-
P0076 J. Teräväinen, arXiv 1611.08585, Lemma 5.2, page 18, quoting Matomäki and Shao Lemma 7.4.
The leaf `twisted_interval_bound` of `Lemma52Split1122b` split into the two standard steps of its
proof: the geometric sum bound `|∑_{n ∈ S} e(γ n)| ≤ 1 / (2 ‖γ‖)` over an interval, and the count
of `Q` frequencies spaced `1/Q` apart, `∑_{a < Q} min(N, 1/(2 ‖a/Q - β‖)) ≪ N + Q √N`.
AI wrote this Lean code, Claude, session CLOUD-S69, burst-20261122. Checked only by the Lean
kernel. The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.Lemma52Split1122b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-! ### Basic facts about `eC` -/

private theorem eC_add_b (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem eC_norm_b (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  rw [Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

private theorem eC_nat_mul_b (k : ℕ) (x : ℝ) : eC ((k : ℝ) * x) = (eC x) ^ k := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem eC_re_b (t : ℝ) : (eC t).re = Real.cos (2 * Real.pi * t) := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re]

private theorem eC_im_b (t : ℝ) : (eC t).im = Real.sin (2 * Real.pi * t) := by
  unfold eC
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_im]

/-- `‖1 - e(t)‖ = 2 |sin π t|`. -/
private theorem norm_one_sub_eC_b (t : ℝ) : ‖1 - eC t‖ = 2 * |Real.sin (Real.pi * t)| := by
  have hsq : ‖1 - eC t‖ ^ 2 = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : (1 - eC t).re = 1 - Real.cos (2 * Real.pi * t) := by
      simp [eC_re_b]
    have h2 : (1 - eC t).im = -Real.sin (2 * Real.pi * t) := by
      simp [eC_im_b]
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

/-- Jordan's inequality in the form needed here: for an integer `m` within `1/2` of `γ`,
`2 |γ - m| ≤ |sin π γ|`. -/
private theorem two_mul_abs_sub_int_le_sin_b {γ : ℝ} (m : ℤ)
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

/-- The geometric sum bound over an order convex range of `ℕ`: for an integer `m` within `1/2`
of `γ`, `‖Σ_{n ∈ S} e(γ n)‖ · 2 |γ - m| ≤ 1`. -/
private theorem geom_sum_norm_b (S : Finset ℕ)
    (hconv : ∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S)
    (γ : ℝ) (m : ℤ) (hm : |γ - (m : ℝ)| ≤ 1 / 2) :
    ‖∑ n ∈ S, eC (γ * n)‖ * (2 * |γ - (m : ℝ)|) ≤ 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set p := S.min' hne with hp
  set q := S.max' hne with hq
  have hSeq : S = Finset.Icc p q := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro n hn
      exact Finset.mem_Icc.2 ⟨Finset.min'_le S n hn, Finset.le_max' S n hn⟩
    · intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
      exact hconv _ (Finset.min'_mem S hne) _ (Finset.max'_mem S hne) n h1 h2
  set L : ℕ := q + 1 - p with hL
  have hsum : ∑ n ∈ S, eC (γ * n) = eC (γ * (p : ℝ)) * ∑ i ∈ Finset.range L, (eC γ) ^ i := by
    rw [hSeq, show Finset.Icc p q = Finset.Ico p (q + 1) by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega, Finset.sum_Ico_eq_sum_range, hL]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show γ * (((p : ℕ) + i : ℕ) : ℝ) = γ * (p : ℝ) + (i : ℝ) * γ by
      push_cast; ring, eC_add_b, eC_nat_mul_b]
  have hnorm : ‖∑ n ∈ S, eC (γ * n)‖ = ‖∑ i ∈ Finset.range L, (eC γ) ^ i‖ := by
    rw [hsum, norm_mul, eC_norm_b, one_mul]
  have htel : (∑ i ∈ Finset.range L, (eC γ) ^ i) * (eC γ - 1) = (eC γ) ^ L - 1 :=
    geom_sum_mul _ _
  have hmain : ‖∑ i ∈ Finset.range L, (eC γ) ^ i‖ * ‖eC γ - 1‖ ≤ 2 := by
    have h2 : ‖(eC γ) ^ L - 1‖ ≤ 2 := by
      calc ‖(eC γ) ^ L - 1‖ ≤ ‖(eC γ) ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, eC_norm_b, norm_one]; norm_num
    calc ‖∑ i ∈ Finset.range L, (eC γ) ^ i‖ * ‖eC γ - 1‖
        = ‖(∑ i ∈ Finset.range L, (eC γ) ^ i) * (eC γ - 1)‖ := by rw [norm_mul]
      _ = ‖(eC γ) ^ L - 1‖ := by rw [htel]
      _ ≤ 2 := h2
  have hden : ‖eC γ - 1‖ = 2 * |Real.sin (Real.pi * γ)| := by
    rw [← norm_neg, neg_sub]
    exact norm_one_sub_eC_b γ
  have hsin : 2 * |γ - (m : ℝ)| ≤ |Real.sin (Real.pi * γ)| := two_mul_abs_sub_int_le_sin_b m hm
  have h3 : ‖∑ i ∈ Finset.range L, (eC γ) ^ i‖ * (2 * |Real.sin (Real.pi * γ)|) ≤ 2 := by
    rw [← hden]
    exact hmain
  rw [hnorm]
  nlinarith [h3, mul_le_mul_of_nonneg_left hsin (norm_nonneg (∑ i ∈ Finset.range L, (eC γ) ^ i)),
    norm_nonneg (∑ i ∈ Finset.range L, (eC γ) ^ i)]

/-- LEAF: the geometric sum bound over an interval, the first step of the dual count in
Matomäki and Shao Lemma 7.4 behind Lemma 5.2, page 18. Class EASY. For `|γ - m| ≤ 1/2`,
`|∑_{n ∈ S} e(γ n)| ≤ 1/|sin π γ| ≤ 1/(2 |γ - m|)`. -/
theorem leaf_geometric_interval : ∀ S : Finset ℕ,
    (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ γ : ℝ, ∀ m : ℤ, |γ - m| ≤ 1 / 2 →
      ‖∑ n ∈ S, eC (γ * n)‖ * (2 * |γ - m|) ≤ 1 := by
  intro S hconv γ m hm
  exact geom_sum_norm_b S hconv γ m hm

/-- Integers with pairwise distances at most `L` number at most `L + 1`. -/
private theorem card_le_of_diam_b (s : Finset ℕ) {L : ℝ} (hL : 0 ≤ L)
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
private theorem count_near_b (Q : ℕ) (hQ : 1 ≤ Q) (β : ℝ) {t : ℝ} (ht0 : 0 < t)
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
    exact card_le_of_diam_b _ (by positivity) (by
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

/-- Every real number is within `1/2` of an integer. -/
private theorem exists_int_abs_sub_le_half_b (x : ℝ) : ∃ m : ℤ, |x - (m : ℝ)| ≤ 1 / 2 := by
  set f : ℤ := ⌊x⌋ with hf
  have h1 : (f : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (f : ℝ) + 1 := Int.lt_floor_add_one x
  rcases le_or_gt (x - (f : ℝ)) (1 / 2) with h | h
  · exact ⟨f, by rw [abs_of_nonneg (by linarith)]; exact h⟩
  · refine ⟨f + 1, ?_⟩
    have hcast : x - (((f : ℤ) + 1 : ℤ) : ℝ) = x - (f : ℝ) - 1 := by push_cast; ring
    rw [hcast, abs_of_neg (by linarith)]
    linarith

/-- The dual count: the `Q` frequencies `a/Q - β` are spaced `1/Q` apart, so all but a set of
`6 t Q + 3` of them keep `g` at most `1/(2t)`. -/
private theorem dual_count_sum_b : ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N → ∀ β : ℝ,
    ∀ g : ℕ → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ N) →
    (∀ a : ℕ, ∀ m : ℤ, |(a : ℝ) / Q - β - m| ≤ 1 / 2 →
      g a * (2 * |(a : ℝ) / Q - β - m|) ≤ 1) →
    ∑ a ∈ range Q, g a ≤ 10 * (N + Q * Real.sqrt N) := by
  intro N Q hQ hNQ β g hg hpt
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have h6 : 6 ≤ 6 * Q ^ 2 := by
    have h1 : 1 ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
    simpa using Nat.mul_le_mul_left 6 h1
  have hN6 : 6 ≤ N := le_trans h6 hNQ
  have hNR6 : (6 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN6
  have hNR : (0 : ℝ) < (N : ℝ) := by linarith
  have hsNpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNR
  have hsN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hNR.le
  have hsN2 : 2 ≤ Real.sqrt (N : ℝ) := by
    have hN4 : (4 : ℝ) ≤ (N : ℝ) := by linarith
    have h4 : Real.sqrt 4 = (2 : ℝ) :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    calc (2 : ℝ) = Real.sqrt 4 := h4.symm
      _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hN4
  set t : ℝ := 1 / Real.sqrt (N : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 2 := by
    rw [ht]
    exact one_div_le_one_div_of_le (by norm_num) hsN2
  set Near : Finset ℕ :=
    (Finset.range Q).filter (fun a : ℕ => ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t) with hNear
  set Far : Finset ℕ :=
    (Finset.range Q).filter (fun a : ℕ => ¬ ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t) with hFar
  have hcard : (Near.card : ℝ) ≤ 6 * t * Q + 3 := by
    rw [hNear]
    exact count_near_b Q hQ β ht0 ht1
  have htN : t * (N : ℝ) = Real.sqrt (N : ℝ) := by
    rw [ht]
    field_simp
    rw [pow_two]
    exact hsN.symm
  have hnear : ∑ a ∈ Near, g a ≤ 6 * (Q : ℝ) * Real.sqrt (N : ℝ) + 3 * (N : ℝ) := by
    have h1 : ∑ a ∈ Near, g a ≤ (Near.card : ℝ) * (N : ℝ) := by
      calc ∑ a ∈ Near, g a ≤ ∑ a ∈ Near, (N : ℝ) := Finset.sum_le_sum fun a _ => (hg a).2
        _ = (Near.card : ℝ) * (N : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : (Near.card : ℝ) * (N : ℝ) ≤ (6 * t * Q + 3) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hcard hNR.le
    have h3 : (6 * t * Q + 3) * (N : ℝ) = 6 * (Q : ℝ) * Real.sqrt (N : ℝ) + 3 * (N : ℝ) := by
      calc (6 * t * Q + 3) * (N : ℝ) = 6 * (t * (N : ℝ)) * (Q : ℝ) + 3 * (N : ℝ) := by ring
        _ = 6 * (Q : ℝ) * Real.sqrt (N : ℝ) + 3 * (N : ℝ) := by rw [htN]; ring
    linarith
  have hfar : ∑ a ∈ Far, g a ≤ (Q : ℝ) * (1 / (2 * t)) := by
    have hb : ∀ a ∈ Far, g a ≤ 1 / (2 * t) := by
      intro a ha
      have hnot : ¬ ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t := (Finset.mem_filter.mp ha).2
      obtain ⟨m, hm⟩ := exists_int_abs_sub_le_half_b ((a : ℝ) / Q - β)
      have hgt : t < |(a : ℝ) / Q - β - (m : ℝ)| := not_le.1 (mt (fun hh => ⟨m, hh⟩) hnot)
      have hpt' := hpt a m hm
      have h2t : 0 < 2 * t := by linarith
      rw [le_div_iff₀ h2t]
      calc g a * (2 * t) ≤ g a * (2 * |(a : ℝ) / Q - β - (m : ℝ)|) := by
            refine mul_le_mul_of_nonneg_left ?_ (hg a).1
            linarith
        _ ≤ 1 := hpt'
    have hcard2 : (Far.card : ℝ) ≤ (Q : ℝ) := by
      have h1 : Far.card ≤ Q := by
        calc Far.card ≤ (Finset.range Q).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = Q := Finset.card_range Q
      exact_mod_cast h1
    calc ∑ a ∈ Far, g a ≤ ∑ a ∈ Far, (1 / (2 * t)) := Finset.sum_le_sum hb
      _ = (Far.card : ℝ) * (1 / (2 * t)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * (1 / (2 * t)) :=
          mul_le_mul_of_nonneg_right hcard2 (by positivity)
  have hsplit : ∑ a ∈ range Q, g a = ∑ a ∈ Near, g a + ∑ a ∈ Far, g a := by
    rw [hNear, hFar]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range Q)
      (fun a : ℕ => ∃ k : ℤ, |(a : ℝ) / Q - β - (k : ℝ)| ≤ t) g).symm
  have h2t : 1 / (2 * t) = Real.sqrt (N : ℝ) / 2 := by
    rw [ht]
    field_simp
  have hfar' : ∑ a ∈ Far, g a ≤ (Q : ℝ) * Real.sqrt (N : ℝ) / 2 := by
    rw [h2t] at hfar
    linarith
  rw [hsplit]
  nlinarith [hnear, hfar', hQpos, hsNpos]

/-- LEAF: the count of the `Q` frequencies `a/Q - β`, spaced `1/Q` apart modulo one, the second
step of the dual count in Matomäki and Shao Lemma 7.4 behind Lemma 5.2, page 18. Class MEDIUM.
`∑_{a < Q} min(N, 1/(2 ‖a/Q - β‖)) ≤ 2N + Q (1 + log Q)`, at most `K (N + Q √N)` once
`6 Q² ≤ N`. -/
theorem leaf_dual_count : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N → ∀ β : ℝ,
    ∀ g : ℕ → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ N) →
    (∀ a : ℕ, ∀ m : ℤ, |(a : ℝ) / Q - β - m| ≤ 1 / 2 → g a * (2 * |(a : ℝ) / Q - β - m|) ≤ 1) →
    ∑ a ∈ range Q, g a ≤ K * (N + Q * Real.sqrt N) := by
  refine ⟨10, by norm_num, ?_⟩
  exact dual_count_sum_b

/-- `twisted_interval_bound` from the two leaves. -/
theorem twisted_interval_bound_of_leaves : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
    ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
      K * (N + Q * Real.sqrt N) := by
  obtain ⟨K, hK, hKb⟩ := leaf_dual_count
  refine ⟨K, hK, fun N Q hQ hNQ S hS hconv β => ?_⟩
  refine hKb N Q hQ hNQ β (fun a => ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖) (fun a => ?_)
    (fun a m hm => leaf_geometric_interval S hconv _ m hm)
  refine ⟨norm_nonneg _, ?_⟩
  calc ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤ ∑ n ∈ S, ‖eC (((a : ℝ) / Q - β) * n)‖ :=
        norm_sum_le _ _
    _ = #S := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        unfold eC
        rw [Complex.norm_exp]
        have h : (2 * (Real.pi : ℂ) * Complex.I * ((((a : ℝ) / Q - β) * n : ℝ) : ℂ)).re = 0 := by
          simp
        rw [h, Real.exp_zero, Nat.cast_one]
    _ ≤ N := by
        have := Finset.card_le_card hS
        rw [Finset.card_range] at this
        exact_mod_cast this

theorem twisted_interval_bound_twin :
    type_of% @LeanLab.Teravainen2016.twisted_interval_bound :=
  twisted_interval_bound_of_leaves

end LeanLab.Teravainen2016
