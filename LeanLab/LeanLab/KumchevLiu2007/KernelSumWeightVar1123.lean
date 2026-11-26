/-
ROUTE BURST burst-20261122, session S154, STEP kernel-sum-split-p3. SPLIT of the MEDIUM LEAF
weight_variation of KernelSumSplitP2, P0088 Kumchev and Liu 2007, page 7, the display before
27, the partial summation in 1/log of the inner window sum.
Two steps, both PROVED in S154, so weight_variation is PROVED:
* window_abs_kernel_sum, PROVED, the l1 size of the kernel over the integer window, at most
  2 + log X, from Kb_zero, Kb_abs_le and the harmonic sum over at most Y + 1 distinct
  integers, Y + 1 at most X.
* log_variation, PROVED, the mean value bound |1/log m1 - 1/log X| at most 4 Y/(X log^2 X) for m1 in
  the window X - Y to X with Y = X^(7/12 + eps/2), for large X.
KernelSumSplitP2.weight_variation is PROVED from them in KernelSumSplitP2. No sorry here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelSumCount1122

namespace LeanLab.KumchevLiu2007.KernelSumWeightVar1123

open Real LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.KernelSumSplit1122
open scoped BigOperators


/-- PROVED, S154. The sum of 1/k over a finite set of positive integers is at most the harmonic
number of its size, by induction on the maximum. -/
theorem sum_inv_pos_le (T : Finset ℤ) (h0 : ∀ k ∈ T, 0 < k) :
    ∑ k ∈ T, 1 / (k : ℝ) ≤ ∑ i ∈ Finset.range T.card, 1 / ((i : ℝ) + 1) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h0s : ∀ k ∈ s, 0 < k := fun k hk => h0 k (Finset.mem_insert_of_mem hk)
    have ha0 : 0 < a := h0 a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, Finset.sum_range_succ]
    have hcard : (s.card : ℤ) + 1 ≤ a := by
      have hsub : s ⊆ Finset.Ioo 0 a := fun x hx => Finset.mem_Ioo.2 ⟨h0s x hx, ha x hx⟩
      have h1 := Finset.card_le_card hsub
      rw [Int.card_Ioo] at h1
      omega
    have h2 : 1 / (a : ℝ) ≤ 1 / ((s.card : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hcard
    linarith [ih h0s]

/-- PROVED, S154. The harmonic number H_N is at most 1 + log N, Mathlib harmonic_le_one_add_log. -/
theorem harm_le (N : ℕ) : ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have e : ((harmonic N : ℚ) : ℝ) = ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) := by
    simp [harmonic, Rat.cast_sum]
  rw [← e]; exact h

/-- PROVED, S154. Harmonic numbers are monotone. -/
theorem harm_mono {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ Finset.range a, 1 / ((i : ℝ) + 1) ≤ ∑ i ∈ Finset.range b, 1 / ((i : ℝ) + 1) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
    (fun i _ _ => by positivity)

/-- PROVED, S154. Pointwise bound of |K_b| by the three parts k = 0, k > 0, k < 0, from Kb_zero
and Kb_abs_le. -/
theorem Kb_pt (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (k : ℤ) :
    |Kb b k| ≤ (if k = 0 then 1 else 0) + (if 0 < k then 1 / π * (1 / (k : ℝ)) else 0) +
      (if 0 < -k then 1 / π * (1 / ((-k : ℤ) : ℝ)) else 0) := by
  have hpi := Real.pi_pos
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h := KernelSumPieces1122.Kb_abs_le b k hk.ne
    have hk' : (k : ℝ) < 0 := by exact_mod_cast hk
    rw [abs_of_neg hk'] at h
    simp only [hk.ne, ite_false, show ¬ (0 < k) by omega, show 0 < -k by omega, ite_true]
    push_cast
    calc |Kb b k| ≤ 1 / (π * -(k : ℝ)) := h
      _ = 0 + 0 + 1 / π * (1 / -(k : ℝ)) := by rw [one_div_mul_one_div]; ring
  · subst hk
    rw [KernelSumPieces1122.Kb_zero]; simp
    rw [abs_le]; constructor <;> linarith
  · have h := KernelSumPieces1122.Kb_abs_le b k hk.ne'
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [abs_of_pos hk'] at h
    simp only [hk.ne', ite_false, hk, ite_true, show ¬ (0 < -k) by omega]
    calc |Kb b k| ≤ 1 / (π * (k : ℝ)) := h
      _ = 0 + 1 / π * (1 / (k : ℝ)) + 0 := by rw [one_div_mul_one_div]; ring

/-- PROVED, S154. The k > 0 part of the window sum is at most H_N / pi. -/
theorem pos_part (W : Finset ℕ) (c : ℤ) :
    ∑ m ∈ W, (if 0 < c + (m : ℤ) then 1 / π * (1 / ((c + (m : ℤ) : ℤ) : ℝ)) else 0) ≤
      1 / π * ∑ i ∈ Finset.range W.card, 1 / ((i : ℝ) + 1) := by
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun m : ℕ => c + (m : ℤ)) (W.filter (fun m : ℕ => 0 < c + (m : ℤ))) := by
    intro x _ y _ h; simp only at h; omega
  rw [← Finset.sum_image (g := fun m : ℕ => c + (m : ℤ)) (f := fun k : ℤ => 1 / (k : ℝ)) hinj]
  have hpi := Real.pi_pos
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (sum_inv_pos_le _ ?_).trans (harm_mono ?_)
  · intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hk
    exact (Finset.mem_filter.1 hm).2
  · exact Finset.card_image_le.trans (Finset.card_filter_le _ _)

/-- PROVED, S154. The k < 0 part of the window sum is at most H_N / pi. -/
theorem neg_part (W : Finset ℕ) (c : ℤ) :
    ∑ m ∈ W, (if 0 < -(c + (m : ℤ)) then 1 / π * (1 / ((-(c + (m : ℤ)) : ℤ) : ℝ)) else 0) ≤
      1 / π * ∑ i ∈ Finset.range W.card, 1 / ((i : ℝ) + 1) := by
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun m : ℕ => -(c + (m : ℤ)))
      (W.filter (fun m : ℕ => 0 < -(c + (m : ℤ)))) := by
    intro x _ y _ h; simp only at h; omega
  rw [← Finset.sum_image (g := fun m : ℕ => -(c + (m : ℤ))) (f := fun k : ℤ => 1 / (k : ℝ)) hinj]
  have hpi := Real.pi_pos
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (sum_inv_pos_le _ ?_).trans (harm_mono ?_)
  · intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hk
    exact (Finset.mem_filter.1 hm).2
  · exact Finset.card_image_le.trans (Finset.card_filter_le _ _)

/-- PROVED, S154. At most one m in the window has c + m = 0. -/
theorem zero_part (W : Finset ℕ) (c : ℤ) :
    ∑ m ∈ W, (if c + (m : ℤ) = 0 then (1 : ℝ) else 0) ≤ 1 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (W.filter (fun m : ℕ => c + (m : ℤ) = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have := (Finset.mem_filter.1 hx).2; have := (Finset.mem_filter.1 hy).2; omega
  exact_mod_cast this

/-- PROVED, S154. The integer window [X - Y, X) has at most X elements when X - Y is at least 1. -/
theorem window_card (X Y : ℝ) (hX : 1 ≤ X) (hXY : 1 ≤ X - Y) : ((primeWindow X Y).card : ℝ) ≤ X := by
  have hsub : primeWindow X Y ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro m hm
    have h := (Finset.mem_filter.1 hm).2
    rw [Finset.mem_Icc]
    constructor
    · have : (0 : ℝ) < m := by linarith [h.1]
      exact_mod_cast this
    · exact Nat.le_floor h.2.le
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h1
  have h2 : ((primeWindow X Y).card : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast (by omega : _ ≤ ⌊X⌋₊)
  exact h2.trans (Nat.floor_le (by linarith))

/-- PROVED, S154. P0088 page 7, the display before 27, weight_variation, the l1 size of the
kernel over the window. |K_b of 0| = |1 - 2b| at most 1 for b in [0, 1], and |K_b of k| at
most 1/(pi |k|) otherwise by Kb_abs_le; the window holds at most Y + 1 at most X distinct
integers, so the sum is at most 1 + (2/pi)(1 + log X), at most 2 + log X. -/
theorem window_abs_kernel_sum :
    ∀ b : ℝ, 0 ≤ b → b ≤ 1 → ∀ X Y : ℝ, 1 ≤ X → 1 ≤ X - Y → ∀ n m2 : ℕ,
      ∑ m1 ∈ primeWindow X Y, |Kb b (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ))| ≤
        2 + Real.log X := by
  intro b hb0 hb1 X Y hX hXY n m2
  set c : ℤ := -(n : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) with hc
  set W := primeWindow X Y with hW
  have e : ∀ m1 : ℕ, -(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) = c + (m1 : ℤ) := by
    intro m1; rw [hc]; ring
  simp_rw [e]
  have hpt := fun m1 : ℕ => Kb_pt b hb0 hb1 (c + (m1 : ℤ))
  refine (Finset.sum_le_sum fun m1 _ => hpt m1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 := zero_part W c
  have h2 := pos_part W c
  have h3 := neg_part W c
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hH := harm_le W.card
  have hlogN : Real.log (W.card : ℝ) ≤ Real.log X := by
    rcases Nat.eq_zero_or_pos W.card with h0 | h0
    · rw [h0]; simpa using hlogX
    · exact Real.log_le_log (by exact_mod_cast h0) (window_card X Y hX hXY)
  have hpi := Real.pi_gt_three
  have hpi0 : (0 : ℝ) < 1 / π := by positivity
  have hpi1 : 1 / π ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hpi.le
  have hS0 : 0 ≤ ∑ i ∈ Finset.range W.card, 1 / ((i : ℝ) + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hS : ∑ i ∈ Finset.range W.card, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log X := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hS hpi0.le, mul_le_mul_of_nonneg_right hpi1 hS0]

/-- PROVED, S154. P0088 page 7, the display before 27, weight_variation, the mean value bound
for 1/log. For m1 in [X - Y, X) with Y = X^(7/12 + eps/2) at most X/2 one has
log X - log m1 at most Y/(X - Y) at most 2Y/X and log m1 at least log X / 2, so
|1/log m1 - 1/log X| at most 4 Y/(X log^2 X), for large X. -/
theorem log_variation :
    ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ∀ m1 ∈ primeWindow X (windowY X ε),
        |1 / Real.log (m1 : ℝ) - 1 / Real.log X| ≤ 4 * (windowY X ε / X) / Real.log X ^ 2 := by
  intro ε hε hε'
  have h2 := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 2 / 9)).eventually_ge_atTop 2
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 h2
  refine ⟨max X1 4, fun X hX m1 hm => ?_⟩
  have hB : (2 : ℝ) ≤ X ^ (2 / 9 : ℝ) := hX1 X (le_trans (le_max_left _ _) hX)
  have hX4 : 4 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  set Y := windowY X ε with hYdef
  have hY9 : Y ≤ X ^ (7 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hsplit : X ^ (7 / 9 : ℝ) * X ^ (2 / 9 : ℝ) = X := by
    rw [← Real.rpow_add hX0]; norm_num
  have h79 : 0 ≤ X ^ (7 / 9 : ℝ) := Real.rpow_nonneg hX0.le _
  have hYnn : 0 ≤ Y := Real.rpow_nonneg hX0.le _
  have hYX2 : 2 * Y ≤ X := by nlinarith [mul_le_mul_of_nonneg_left hB h79]
  have hmw := (Finset.mem_filter.1 hm).2
  have hm0 : X / 2 ≤ (m1 : ℝ) := by linarith [hmw.1]
  have hmpos : 0 < (m1 : ℝ) := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog4 : 2 * Real.log 2 ≤ Real.log X := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 4) hX4
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    push_cast at h; linarith
  have hlm : Real.log X / 2 ≤ Real.log (m1 : ℝ) := by
    have h := Real.log_le_log (by linarith) hm0
    rw [Real.log_div hX0.ne' (by norm_num)] at h
    linarith
  have hlm0 : 0 < Real.log (m1 : ℝ) := by linarith
  have hd0 : 0 ≤ Real.log X - Real.log (m1 : ℝ) := by
    have := Real.log_le_log hmpos hmw.2.le; linarith
  have hd : Real.log X - Real.log (m1 : ℝ) ≤ 2 * (Y / X) := by
    rw [← Real.log_div hX0.ne' hmpos.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hX0 hmpos)
    have h3 : X / (m1 : ℝ) - 1 ≤ 2 * (Y / X) := by
      rw [div_sub_one hmpos.ne', mul_div_assoc', div_le_div_iff₀ hmpos hX0]
      nlinarith [hmw.1, hmw.2, hm0, hYnn]
    linarith
  have he : 1 / Real.log (m1 : ℝ) - 1 / Real.log X =
      (Real.log X - Real.log (m1 : ℝ)) / (Real.log (m1 : ℝ) * Real.log X) := by
    field_simp
  have hYX : 0 ≤ Y / X := div_nonneg hYnn hX0.le
  rw [he, abs_of_nonneg (div_nonneg hd0 (mul_pos hlm0 hL).le),
    div_le_div_iff₀ (mul_pos hlm0 hL) (pow_pos hL 2)]
  have hc : (0:ℝ) ≤ 4 * (Y / X) * Real.log X := mul_nonneg (mul_nonneg (by norm_num) hYX) hL.le
  nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg (Real.log X)),
    mul_le_mul_of_nonneg_left hlm hc]

end LeanLab.KumchevLiu2007.KernelSumWeightVar1123

#print axioms LeanLab.KumchevLiu2007.KernelSumWeightVar1123.window_abs_kernel_sum
#print axioms LeanLab.KumchevLiu2007.KernelSumWeightVar1123.log_variation
