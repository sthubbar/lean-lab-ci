/-
ROUTE BURST burst-20261124, session S1, follow-on split of unit S1-01, route of
Task628.major_arc_block. SPLIT of the LEAF KernelIcoSplit1124.kernel_Ico_far,
P0088 Kumchev and Liu 2007, page 7, the display before 27.

1. sawtooth_rate, LEAF HARD: the symmetric partial sums of K_b tend to 0 at rate
   O(1/(b N)), the sawtooth Fourier series 1 - 2b = 2 times the sum over k at least 1 of
   sin(2 pi k b)/(pi k) with its Abel tail.
2. signedPrefix_step, signedPrefix_tel, signedPrefix_near_half, PROVED: every run of K_b is
   a difference of two signed prefix sums, each within C/(b (|n| + 1)) of K_b(0)/2.
3. kernel_Ico_far_of_sawtooth, PROVED; kernel_Ico_far_split has the exact type of
   kernel_Ico_far, CONDITIONAL ON sawtooth_rate; kernel_Ico_sum_bound_split2 and
   inner_window_bound_split2 have the exact types of InnerWindowSplit1124.kernel_Ico_sum_bound
   and KernelSumSplit1122.inner_window_bound, CONDITIONAL ON sawtooth_rate only.
New definition: signedPrefix.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelIcoSplit1124

namespace LeanLab.KumchevLiu2007.KernelFarSplit1124

open Real LeanLab.KumchevLiu2007.KernelSumSplit1122 LeanLab.KumchevLiu2007.KernelSumPieces1122
open LeanLab.KumchevLiu2007.InnerWindowSplit1124 LeanLab.KumchevLiu2007.KernelIcoSplit1124
open scoped BigOperators

/-- The signed prefix sum of K_b, the partial sums of the kernel of P0088 page 7, the
display before 27: the sum over 0 to n - 1 for n at least 0, and minus the sum over n to -1
for n below 0, so that every run of K_b is a difference of two values. -/
noncomputable def signedPrefix (b : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then ∑ i ∈ Finset.range n.toNat, Kb b (i : ℤ)
    else -∑ i ∈ Finset.range (-n).toNat, Kb b (-((i : ℤ) + 1))

/-- PROVED. Consecutive signed prefix sums differ by K_b. -/
theorem signedPrefix_step (b : ℝ) (n : ℤ) :
    signedPrefix b (n + 1) - signedPrefix b n = Kb b n := by
  rcases le_or_gt 0 n with hn | hn
  · have h1 : 0 ≤ n + 1 := by omega
    simp only [signedPrefix, if_pos hn, if_pos h1]
    rw [show (n + 1).toNat = n.toNat + 1 by omega, Finset.sum_range_succ]
    rw [Int.toNat_of_nonneg hn]; ring
  · rcases eq_or_lt_of_le (show n + 1 ≤ 0 by omega) with h0 | h0
    · have hn1 : n = -1 := by omega
      subst hn1
      simp [signedPrefix]
    · have h1 : ¬ 0 ≤ n + 1 := by omega
      have h2 : ¬ 0 ≤ n := by omega
      simp only [signedPrefix, if_neg h1, if_neg h2]
      rw [show (-n).toNat = (-(n + 1)).toNat + 1 by omega, Finset.sum_range_succ]
      have : -(((-(n + 1)).toNat : ℤ) + 1) = n := by omega
      rw [this]; ring

/-- PROVED. A run of K_b is a difference of two signed prefix sums. -/
theorem signedPrefix_tel (b : ℝ) (A : ℤ) (L : ℕ) :
    ∑ i ∈ Finset.range L, Kb b (A + i) = signedPrefix b (A + L) - signedPrefix b A := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, ← signedPrefix_step b (A + L)]
    push_cast; ring_nf

/-- PROVED. Given the sawtooth rate with constant C, every signed prefix sum at n is within
C/(b (|n| + 1)) of K_b(0)/2. -/
theorem signedPrefix_near_half (b : ℝ) (hb : 0 < b) (C : ℝ) (hC : 0 ≤ C)
    (hsaw : ∀ N : ℕ, |Kb b 0 + 2 * ∑ i ∈ Finset.range N, Kb b ((1 + i : ℕ) : ℤ)| ≤
      C / (b * (N + 1))) (n : ℤ) :
    |signedPrefix b n - Kb b 0 / 2| ≤ C / (b * (|(n : ℝ)| + 1)) := by
  by_cases hn : 0 ≤ n
  · rcases eq_or_lt_of_le hn with h0 | h0
    · subst h0
      have := hsaw 0
      simp only [signedPrefix, le_refl, if_true, Int.toNat_zero, Finset.range_zero,
        Finset.sum_empty, mul_zero, add_zero, Int.cast_zero, abs_zero, zero_add, CharP.cast_eq_zero] at this ⊢
      rw [zero_sub, abs_neg, abs_div, abs_two]
      have hc : 0 ≤ C / b := by positivity
      rw [mul_one]
      rw [mul_one] at this
      linarith [abs_nonneg (Kb b 0)]
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
      have e : signedPrefix b n = Kb b 0 + ∑ i ∈ Finset.range m, Kb b ((1 + i : ℕ) : ℤ) := by
        simp only [signedPrefix, if_pos hn]
        rw [show n.toNat = m + 1 by omega, Finset.sum_range_succ']
        rw [add_comm]; congr 1
        refine Finset.sum_congr rfl fun i _ => ?_; congr 1; push_cast; ring
      have hs := hsaw m
      rw [e, show Kb b 0 + ∑ i ∈ Finset.range m, Kb b ((1 + i : ℕ) : ℤ) - Kb b 0 / 2 =
        (Kb b 0 + 2 * ∑ i ∈ Finset.range m, Kb b ((1 + i : ℕ) : ℤ)) / 2 by ring, abs_div, abs_two]
      have hn' : |(n : ℝ)| + 1 = (m : ℝ) + 2 := by
        rw [hm]; push_cast; rw [abs_of_nonneg (by positivity)]; ring
      rw [hn']
      have h2 : C / (b * ((m : ℝ) + 1)) / 2 ≤ C / (b * ((m : ℝ) + 2)) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ C * b := by positivity
        nlinarith
      linarith [div_le_div_of_nonneg_right hs (show (0:ℝ) ≤ 2 by norm_num)]
  · push Not at hn
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    have e : signedPrefix b n = -∑ i ∈ Finset.range (m + 1), Kb b ((1 + i : ℕ) : ℤ) := by
      simp only [signedPrefix, if_neg (not_le.mpr hn)]
      rw [show (-n).toNat = m + 1 by omega]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Kb_neg]; push_cast; ring_nf
    have hs := hsaw (m + 1)
    rw [e, show -∑ i ∈ Finset.range (m + 1), Kb b ((1 + i : ℕ) : ℤ) - Kb b 0 / 2 =
      -((Kb b 0 + 2 * ∑ i ∈ Finset.range (m + 1), Kb b ((1 + i : ℕ) : ℤ)) / 2) by ring,
      abs_neg, abs_div, abs_two]
    have hn' : |(n : ℝ)| + 1 = ((m + 1 : ℕ) : ℝ) + 1 := by
      rw [hm]; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [hn']
    have : 0 ≤ C / (b * (((m + 1 : ℕ) : ℝ) + 1)) := by positivity
    linarith

/-- LEAF: P0088 page 7, the display before 27, the sawtooth series behind the kernel K_b,
with a rate. HARD. For 0 < b at most 1/4 the symmetric partial sum of K_b over |k| at most
N, which is 1 - 2b minus 2 times the sum over k from 1 to N of sin(2 pi k b)/(pi k), is at
most C/(b (N + 1)). Proof sketch: the Fourier series of the sawtooth gives the sum over all
k at least 1 of sin(2 pi k b)/(pi k) = 1/2 - b for 0 < b < 1, so the partial sum is 2 times
the tail beyond N, and the tail is at most 1/(pi (N + 1)) times 1/(2b) by
KernelIcoSplit1124.tail_abel. -/
theorem sawtooth_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ N : ℕ,
      |Kb b 0 + 2 * ∑ i ∈ Finset.range N, Kb b ((1 + i : ℕ) : ℤ)| ≤ C / (b * (N + 1)) := by
  sorry

/-- PROVED. The far bound of the kernel over an integer interval from the sawtooth rate,
with C2 = 2C: both signed prefix sums at the ends are near K_b(0)/2. -/
theorem kernel_Ico_far_of_sawtooth
    (hsaw : ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ N : ℕ,
      |Kb b 0 + 2 * ∑ i ∈ Finset.range N, Kb b ((1 + i : ℕ) : ℤ)| ≤ C / (b * (N + 1))) :
    type_of% @LeanLab.KumchevLiu2007.KernelIcoSplit1124.kernel_Ico_far := by
  obtain ⟨C, hC, hs⟩ := hsaw
  refine ⟨2 * C, by positivity, ?_⟩
  intro b hb hb' c M1 M2
  set d := min |(c : ℝ) + M1| |(c : ℝ) + M2| with hd
  have hd0 : 0 ≤ d := le_min (abs_nonneg _) (abs_nonneg _)
  by_cases hM : M2 ≤ M1
  · rw [Finset.Ico_eq_empty_of_le hM, Finset.sum_empty, abs_zero]; positivity
  push Not at hM
  rw [Finset.sum_Ico_eq_sum_range]
  have e : ∑ k ∈ Finset.range (M2 - M1), Kb b (c + ((M1 + k : ℕ) : ℤ)) =
      ∑ k ∈ Finset.range (M2 - M1), Kb b ((c + M1) + (k : ℤ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_; push_cast; ring_nf
  rw [e, signedPrefix_tel, show c + (M1 : ℤ) + ((M2 - M1 : ℕ) : ℤ) = c + M2 by omega]
  have h2 := signedPrefix_near_half b hb C hC.le (hs b hb hb') (c + M2)
  have h1 := signedPrefix_near_half b hb C hC.le (hs b hb hb') (c + M1)
  push_cast at h1 h2
  have k1 : C / (b * (|(c : ℝ) + M1| + 1)) ≤ C / (b * (d + 1)) := by
    gcongr; exact min_le_left _ _
  have k2 : C / (b * (|(c : ℝ) + M2| + 1)) ≤ C / (b * (d + 1)) := by
    gcongr; exact min_le_right _ _
  have := abs_sub_le (signedPrefix b (c + M2)) (Kb b 0 / 2) (signedPrefix b (c + M1))
  rw [abs_sub_comm (Kb b 0 / 2)] at this
  calc _ ≤ C / (b * (d + 1)) + C / (b * (d + 1)) := by linarith
    _ = 2 * C / (b * (d + 1)) := by ring

/-- CONDITIONAL ON sawtooth_rate: the exact type of KernelIcoSplit1124.kernel_Ico_far. -/
theorem kernel_Ico_far_split : type_of% @LeanLab.KumchevLiu2007.KernelIcoSplit1124.kernel_Ico_far :=
  kernel_Ico_far_of_sawtooth sawtooth_rate

/-- CONDITIONAL ON sawtooth_rate: the exact type of InnerWindowSplit1124.kernel_Ico_sum_bound. -/
theorem kernel_Ico_sum_bound_split2 :
    type_of% @LeanLab.KumchevLiu2007.InnerWindowSplit1124.kernel_Ico_sum_bound :=
  kernel_Ico_sum_bound_of_pieces kernel_Ico_uniform kernel_Ico_far_split

/-- CONDITIONAL ON sawtooth_rate: the exact type of KernelSumSplit1122.inner_window_bound. -/
theorem inner_window_bound_split2 :
    type_of% @LeanLab.KumchevLiu2007.KernelSumSplit1122.inner_window_bound :=
  inner_window_bound_of_pieces kernel_Ico_sum_bound_split2 log_weight_bounds bq_small

end LeanLab.KumchevLiu2007.KernelFarSplit1124

#print axioms LeanLab.KumchevLiu2007.KernelFarSplit1124.signedPrefix_step
#print axioms LeanLab.KumchevLiu2007.KernelFarSplit1124.signedPrefix_tel
#print axioms LeanLab.KumchevLiu2007.KernelFarSplit1124.signedPrefix_near_half
#print axioms LeanLab.KumchevLiu2007.KernelFarSplit1124.kernel_Ico_far_of_sawtooth
#print axioms LeanLab.KumchevLiu2007.KernelFarSplit1124.kernel_Ico_far_split
#print axioms LeanLab.KumchevLiu2007.KernelFarSplit1124.inner_window_bound_split2
