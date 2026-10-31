/-
I-0061, full range, run 20261017T1103Z-22220, unit U-0291. AI-written Lean code, Claude.
Checked only by the Lean kernel.

From Siegel-Walfisz alone: for every C > 0, all but O(X (log X)^{-C}) even m ≤ X have
r(m) ≥ e⁻⁶ m / (12 log² m). Proof: cover (X q^J, X] with q = 2/3 by the intervals
(2x_k, 3x_k], x_k = (X/3) q^k, k < J, where q^J is about (log X)^{-C}; apply
`lowRepsM_card_of_siegelWalfisz` on each and sum the geometric series.
KNOWN mathematics. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.HeathBrown1985.RightOrder

noncomputable section
namespace LeanLab.HeathBrown1985

open Finset Real Filter

attribute [local instance] Classical.propDecidable

/-- The even `m ≤ X`, `m ≥ 4`, with `r(m) < e⁻⁶ m / (12 log² m)`. -/
def lowUpTo (X : ℝ) : Finset ℕ :=
  (range (⌊X⌋₊ + 1)).filter (fun m => Even m ∧ 4 ≤ m ∧
      (LeanLab.SchnirelmannGoldbach.r m : ℝ) < Real.exp (-6) * m / (12 * Real.log m ^ 2))

/-- A power of `q ∈ (0, 1)` lands in `(q t, t]` for every `t ∈ (0, 1]`. -/
lemma exists_pow_between {q t : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ J : ℕ, q ^ J ≤ t ∧ q * t < q ^ J := by
  have hex : ∃ n : ℕ, q ^ n ≤ t := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ht0 hq1
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | j
  · simp only [pow_zero]; nlinarith
  · have hj : ¬ q ^ j ≤ t := Nat.find_min hex (by omega)
    push_neg at hj
    rw [pow_succ]
    nlinarith

/-- The intervals `(X q^{k+1}, X q^k]`, `k < J`, cover `(X q^J, X]`. -/
lemma cover {q X m : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hX : 0 < X) :
    ∀ J : ℕ, X * q ^ J < m → m ≤ X → ∃ k < J, X * q ^ (k + 1) < m ∧ m ≤ X * q ^ k := by
  intro J
  induction J with
  | zero => intro h1 h2; simp at h1; linarith
  | succ j ih =>
    intro h1 h2
    by_cases hm : X * q ^ j < m
    · obtain ⟨k, hk, hk'⟩ := ih hm h2
      exact ⟨k, by omega, hk'⟩
    · push_neg at hm
      exact ⟨j, by omega, h1, hm⟩

theorem lowUpTo_card_of_siegelWalfisz (hSW : SiegelWalfisz) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X → ((lowUpTo X).card : ℝ) ≤ K * X * Real.log X ^ (-C) := by
  obtain ⟨K1, hK1⟩ := lowRepsM_card_of_siegelWalfisz hSW C hC
  set K1' := max K1 0
  -- eventually (log X)^C ≤ √X / 3
  have hlo := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp hlo
  set X0 := max (max X1 16) 3
  set q : ℝ := 2 / 3
  have hq0 : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  refine ⟨max (2 + K1' * 2 ^ C * 2) (2 * Real.log X0 ^ C), fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  have hLC : 0 < Real.log X ^ C := Real.rpow_pos_of_pos hL0 C
  have hLmC : Real.log X ^ (-C) = (Real.log X ^ C)⁻¹ := Real.rpow_neg hL0.le C
  have htriv : ((lowUpTo X).card : ℝ) ≤ X + 1 := by
    have : (lowUpTo X).card ≤ ⌊X⌋₊ + 1 := (card_filter_le _ _).trans (by simp)
    have h2 : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
    calc ((lowUpTo X).card : ℝ) ≤ ((⌊X⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ X + 1 := by push_cast; linarith
  by_cases hsmall : X ≤ X0
  · -- bounded range: trivial bound
    have hlX : Real.log X ≤ Real.log X0 := Real.log_le_log hX0 hsmall
    have hpow : Real.log X ^ C ≤ Real.log X0 ^ C :=
      Real.rpow_le_rpow hL0.le hlX hC.le
    have hone : 1 ≤ Real.log X0 ^ C * Real.log X ^ (-C) := by
      rw [hLmC, ← div_eq_mul_inv, le_div_iff₀ hLC]; linarith
    calc ((lowUpTo X).card : ℝ) ≤ X + 1 := htriv
      _ ≤ 2 * X := by linarith
      _ ≤ 2 * X * (Real.log X0 ^ C * Real.log X ^ (-C)) := by nlinarith
      _ = (2 * Real.log X0 ^ C) * X * Real.log X ^ (-C) := by ring
      _ ≤ max (2 + K1' * 2 ^ C * 2) (2 * Real.log X0 ^ C) * X * Real.log X ^ (-C) := by
          gcongr; exact le_max_right _ _
  push_neg at hsmall
  have hXX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsmall.le
  have hX16 : 16 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsmall.le
  have hb := hX1 X hXX1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLC,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at hb
  have hsq : X ^ (1 / 2 : ℝ) = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  rw [hsq] at hb
  -- t = (log X)^{-C} ≤ 1
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have ht1 : Real.log X ^ (-C) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have ht0 : 0 < Real.log X ^ (-C) := Real.rpow_pos_of_pos hL0 _
  obtain ⟨J, hJ1, hJ2⟩ := exists_pow_between hq0 hq1 ht0 ht1
  set t := Real.log X ^ (-C)
  have hsqX : 4 ≤ Real.sqrt X := by
    rw [Real.le_sqrt (by norm_num) hX0.le]; linarith
  have hsqpos : 0 < Real.sqrt X := by linarith
  have hsq2 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  -- X t / 3 ≥ √X
  have hXt : Real.sqrt X ≤ X * t / 3 := by
    have : t = (Real.log X ^ C)⁻¹ := hLmC
    rw [this, le_div_iff₀ (by norm_num), ← div_eq_mul_inv, le_div_iff₀ hLC]
    nlinarith
  -- each x_k ≥ √X
  set x : ℕ → ℝ := fun k => X / 3 * q ^ k
  have hxk : ∀ k < J, Real.sqrt X ≤ x k := by
    intro k hk
    have : q ^ J ≤ q ^ (k + 1) := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
    have h2 : q * t < q * q ^ k := by rw [pow_succ] at this; nlinarith
    have h3 : t < q ^ k := lt_of_mul_lt_mul_left h2 hq0.le
    simp only [x]; nlinarith
  have hx2 : ∀ k < J, 2 ≤ x k := fun k hk => by linarith [hxk k hk]
  have hlogx : ∀ k < J, Real.log X / 2 ≤ Real.log (x k) := by
    intro k hk
    have h1 := Real.log_le_log hsqpos (hxk k hk)
    rwa [Real.log_sqrt hX0.le] at h1
  have hterm : ∀ k < J, ((lowRepsM (x k)).card : ℝ) ≤ K1' * 2 ^ C * (x k * t) := by
    intro k hk
    have h1 := hK1 (x k) (hx2 k hk)
    have hpos : 0 < Real.log X / 2 := by linarith
    have h2 : Real.log (x k) ^ (-C) ≤ (Real.log X / 2) ^ (-C) :=
      Real.rpow_le_rpow_of_nonpos hpos (hlogx k hk) (by linarith)
    have h3 : (Real.log X / 2) ^ (-C) = 2 ^ C * t := by
      rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_eq_mul_inv, inv_inv]
      ring
    have hxk0 : 0 ≤ x k := by linarith [hx2 k hk]
    have h4 : K1 * x k * Real.log (x k) ^ (-C) ≤ K1' * x k * Real.log (x k) ^ (-C) := by
      have : 0 ≤ x k * Real.log (x k) ^ (-C) :=
        mul_nonneg hxk0 (Real.rpow_nonneg (by linarith [hlogx k hk]) _)
      nlinarith [le_max_left K1 0]
    have h5 : K1' * x k * Real.log (x k) ^ (-C) ≤ K1' * x k * (2 ^ C * t) := by
      rw [← h3]; gcongr
    calc ((lowRepsM (x k)).card : ℝ) ≤ K1 * x k * Real.log (x k) ^ (-C) := h1
      _ ≤ K1' * x k * (2 ^ C * t) := h4.trans h5
      _ = K1' * 2 ^ C * (x k * t) := by ring
  -- the covering
  set Y := X * q ^ J
  have hsub : lowUpTo X ⊆ (range (⌊Y⌋₊ + 1)) ∪ (range J).biUnion (fun k => lowRepsM (x k)) := by
    intro m hm
    simp only [lowUpTo, mem_filter, mem_range] at hm
    obtain ⟨hm1, hev, hm4, hlt⟩ := hm
    by_cases hmY : (m : ℝ) ≤ Y
    · apply mem_union_left; rw [mem_range]
      have := Nat.le_floor hmY; omega
    · push_neg at hmY
      have hmX : (m : ℝ) ≤ X := by
        have : m ≤ ⌊X⌋₊ := by omega
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le hX0.le)
      obtain ⟨k, hk, hk1, hk2⟩ := cover hq0 hq1 hX0 J hmY hmX
      apply mem_union_right
      rw [mem_biUnion]
      refine ⟨k, mem_range.mpr hk, ?_⟩
      simp only [lowRepsM, mem_filter, mem_range]
      have e3 : 3 * x k = X * q ^ k := by simp only [x]; ring
      have e2 : 2 * x k = X * q ^ (k + 1) := by simp only [x, q]; ring
      refine ⟨⟨?_, by rw [e2]; exact hk1⟩, hev, hlt⟩
      have : m ≤ ⌊3 * x k⌋₊ := Nat.le_floor (by rw [e3]; exact hk2)
      omega
  have hcard := card_le_card hsub
  have hY : ((range (⌊Y⌋₊ + 1)).card : ℝ) ≤ X * t + 1 := by
    rw [card_range]; push_cast
    have : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by positivity)
    have : Y ≤ X * t := by simp only [Y]; nlinarith
    linarith
  have hgeom : ∑ k ∈ range J, x k ≤ X := by
    have hg : ∑ k ∈ range J, q ^ k ≤ 3 := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hq0.le hq1
      rw [← range_eq_Ico] at this
      simpa [q] using this.trans (by norm_num [q])
    simp only [x]
    rw [← mul_sum]
    nlinarith
  have hB : (((range J).biUnion (fun k => lowRepsM (x k))).card : ℝ) ≤
      K1' * 2 ^ C * (X * t) := by
    have h1 := card_biUnion_le (s := range J) (t := fun k => lowRepsM (x k))
    have h2 : (∑ k ∈ range J, ((lowRepsM (x k)).card : ℝ)) ≤
        ∑ k ∈ range J, K1' * 2 ^ C * (x k * t) :=
      sum_le_sum fun k hk => hterm k (mem_range.mp hk)
    have h3 : ∑ k ∈ range J, K1' * 2 ^ C * (x k * t) = K1' * 2 ^ C * t * ∑ k ∈ range J, x k := by
      rw [mul_sum]; congr 1; ext k; ring
    have hK0 : 0 ≤ K1' * 2 ^ C * t :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)) ht0.le
    calc (((range J).biUnion (fun k => lowRepsM (x k))).card : ℝ)
        ≤ ∑ k ∈ range J, ((lowRepsM (x k)).card : ℝ) := by exact_mod_cast h1
      _ ≤ K1' * 2 ^ C * t * ∑ k ∈ range J, x k := h2.trans h3.le
      _ ≤ K1' * 2 ^ C * t * X := mul_le_mul_of_nonneg_left hgeom hK0
      _ = K1' * 2 ^ C * (X * t) := by ring
  have hone : 1 ≤ X * t := by
    have : Real.sqrt X ≤ X * t / 3 := hXt
    linarith
  have hU := card_union_le (range (⌊Y⌋₊ + 1)) ((range J).biUnion (fun k => lowRepsM (x k)))
  have hK2 : 0 ≤ K1' * 2 ^ C := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)
  calc ((lowUpTo X).card : ℝ)
      ≤ ((range (⌊Y⌋₊ + 1)).card : ℝ) +
          (((range J).biUnion (fun k => lowRepsM (x k))).card : ℝ) := by
        exact_mod_cast hcard.trans hU
    _ ≤ X * t + 1 + K1' * 2 ^ C * (X * t) := by linarith
    _ ≤ (2 + K1' * 2 ^ C * 2) * X * t := by nlinarith
    _ ≤ max (2 + K1' * 2 ^ C * 2) (2 * Real.log X0 ^ C) * X * t := by
        gcongr; exact le_max_left _ _

/-- **I-0061, full range.** From Siegel-Walfisz alone: `r(m) ≪ m / log² m · ∏_{p ∣ m}(1 + 1/p)`
for every `m ≥ 3`, and for every `C > 0` all but `O(X (log X)^{-C})` even `m ≤ X` have
`r(m) ≥ e⁻⁶ m / (12 log² m)`. So `r(m)` has the order `m / log² m` up to the singular
product for almost all even `m`. Zero sorry. Binary Goldbach is OPEN. -/
theorem rightOrderFull_of_siegelWalfisz (hSW : SiegelWalfisz) :
    (∃ C' : ℝ, ∀ m : ℕ, 3 ≤ m →
      (LeanLab.SchnirelmannGoldbach.r m : ℝ) ≤
        C' * m / Real.log m ^ 2 * LeanLab.SchnirelmannGoldbach.singProd m) ∧
    (∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ X : ℝ, 2 ≤ X →
      ((lowUpTo X).card : ℝ) ≤ K * X * Real.log X ^ (-C)) :=
  ⟨(rightOrder_of_siegelWalfisz hSW).1, lowUpTo_card_of_siegelWalfisz hSW⟩

end LeanLab.HeathBrown1985
