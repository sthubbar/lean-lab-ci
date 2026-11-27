/-
ROUTE BURST burst-20261124, session S1, follow-on split of unit S1-01, route of
Task628.major_arc_block. SPLIT of the LEAF InnerWindowSplit1124.kernel_Ico_sum_bound,
P0088 Kumchev and Liu 2007, page 7, the display before 27.

The bound min 1 (1/(b (d + 1))) of the kernel over an integer interval is the pair of the
two estimates the paper uses there:
1. kernel_Ico_uniform, PROVED, formerly LEAF MEDIUM: the sum of K_b over any integer
   interval is at most 10, from bounded partial sums of sin(2 pi k b)/(pi k).
2. kernel_Ico_far, LEAF HARD: the sum is O(1/(b (d + 1))), d the distance of 0 to the
   interval ends. When 0 lies inside the interval this needs the sawtooth series
   1 - 2b = 2 times the sum over k at least 1 of sin(2 pi k b)/(pi k) for 0 < b < 1.
kernel_Ico_sum_bound_of_pieces, PROVED, combines them; kernel_Ico_sum_bound_split has the
exact type of kernel_Ico_sum_bound and is CONDITIONAL ON kernel_Ico_far only.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.InnerWindowSplit1124

namespace LeanLab.KumchevLiu2007.KernelIcoSplit1124

open Real LeanLab.KumchevLiu2007.KernelSumSplit1122 LeanLab.KumchevLiu2007.KernelSumPieces1122
open LeanLab.KumchevLiu2007.InnerWindowSplit1124
open scoped BigOperators

/-- PROVED. For n at least 1, K_b at n is minus 1/(pi n) times sin(2 pi n b). -/
theorem Kb_pos_eq (b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Kb b (n : ℤ) = -((1 / (π * (n : ℝ))) * Real.sin (2 * (n : ℝ) * (π * b))) := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Kb, hn', ite_false, Int.cast_natCast]
  have : 2 * π * (n : ℝ) * b = 2 * (n : ℝ) * (π * b) := by ring
  rw [this]; ring

/-- PROVED. K_b is even. -/
theorem Kb_neg (b : ℝ) (k : ℤ) : Kb b (-k) = Kb b k := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
    simp only [Kb, hk, hk', ite_false, Int.cast_neg]
    rw [show 2 * π * -(k : ℝ) * b = -(2 * π * (k : ℝ) * b) by ring, Real.sin_neg]
    rw [show π * -(k : ℝ) = -(π * (k : ℝ)) by ring, neg_div_neg_eq]

/-- PROVED. Abel summation of sin(2 pi n b) against 1/(pi n): a run of K_b starting at
a at least 1 is at most 1/(pi a) times 1/(2b), by abel_antitone and abs_sum_sin_le. -/
theorem tail_abel (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1 / 2) (a L : ℕ) (ha : 1 ≤ a) :
    |∑ i ∈ Finset.range L, Kb b ((a + i : ℕ) : ℤ)| ≤ 1 / (π * a) * (1 / (2 * b)) := by
  have hpi := Real.pi_pos
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp; positivity
  obtain ⟨N, rfl⟩ : ∃ N, L = N + 1 := ⟨L - 1, by omega⟩
  set w : ℕ → ℝ := fun n => 1 / (π * (n : ℝ))
  set f : ℕ → ℝ := fun n => Real.sin (2 * (n : ℝ) * (π * b))
  have hsum : ∑ i ∈ Finset.range (N + 1), Kb b ((a + i : ℕ) : ℤ) =
      -∑ i ∈ Finset.range (N + 1), w (a + i) * f (a + i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Kb_pos_eq b (a + i) (by omega)
  rw [hsum, abs_neg]
  have hw : ∀ i j : ℕ, i ≤ j → j ≤ N → w (a + j) ≤ w (a + i) := by
    intro i j hij _
    simp only [w]
    apply one_div_le_one_div_of_le (by positivity)
    have : ((a + i : ℕ) : ℝ) ≤ ((a + j : ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith
  have hpart : ∀ k : ℕ, k ≤ N → |∑ i ∈ Finset.range (k + 1), f (a + i)| ≤ 1 / (2 * b) := by
    intro k _
    have := abs_sum_sin_le b (a : ℝ) (k + 1) hb hb'
    simpa [f, Nat.cast_add] using this
  have h := abel_antitone w f a N (1 / (2 * b)) hw hpart
  have hwN : 0 ≤ w (a + N) := by simp only [w]; positivity
  have hwa : w (a + 0) = 1 / (π * a) := by simp [w]
  have h1 := hpart N le_rfl
  have hS : 0 ≤ 1 / (2 * b) := by positivity
  calc _ ≤ |w (a + N)| * |∑ i ∈ Finset.range (N + 1), f (a + i)| + (w a - w (a + N)) * (1 / (2 * b)) := h
    _ ≤ w (a + N) * (1 / (2 * b)) + (w a - w (a + N)) * (1 / (2 * b)) := by
        rw [abs_of_nonneg hwN]; gcongr
    _ = 1 / (π * a) * (1 / (2 * b)) := by simp only [w]; ring

/-- PROVED. Each K_b at n at least 1 is at most 2b, by sin x at most x. -/
theorem head_bound (b : ℝ) (hb : 0 < b) (a L : ℕ) (ha : 1 ≤ a) :
    |∑ i ∈ Finset.range L, Kb b ((a + i : ℕ) : ℤ)| ≤ L * (2 * b) := by
  have hpi := Real.pi_pos
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ Finset.range L, |Kb b ((a + i : ℕ) : ℤ)| ≤ 2 * b := by
    intro i _
    have hn : (0 : ℝ) < ((a + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < a + i)
    rw [Kb_pos_eq b (a + i) (by omega), abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (π * ((a + i : ℕ) : ℝ)))]
    have hs : |Real.sin (2 * ((a + i : ℕ) : ℝ) * (π * b))| ≤ 2 * ((a + i : ℕ) : ℝ) * (π * b) := by
      have := Real.abs_sin_le_abs (x := 2 * ((a + i : ℕ) : ℝ) * (π * b))
      rwa [abs_of_pos (show (0:ℝ) < 2 * ((a + i : ℕ) : ℝ) * (π * b) by positivity)] at this
    calc _ ≤ 1 / (π * ((a + i : ℕ) : ℝ)) * (2 * ((a + i : ℕ) : ℝ) * (π * b)) := by gcongr
      _ = 2 * b := by field_simp
  refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
  simp

/-- PROVED. A run of K_b over positive integers is at most 4 for 0 < b at most 1/4:
head_bound up to ceil(1/b), tail_abel beyond. -/
theorem pos_bound (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1 / 4) (a L : ℕ) (ha : 1 ≤ a) :
    |∑ i ∈ Finset.range L, Kb b ((a + i : ℕ) : ℤ)| ≤ 4 := by
  have hpi := Real.pi_pos
  set K := ⌈1 / b⌉₊ with hK
  have hK1 : (K : ℝ) < 1 / b + 1 := Nat.ceil_lt_add_one (by positivity)
  have hK0 : 1 / b ≤ (K : ℝ) := Nat.le_ceil _
  have hbK : b * K ≤ b * (1 / b + 1) := by nlinarith
  have hbK' : b * (1 / b + 1) = 1 + b := by field_simp
  by_cases hLK : L ≤ K
  · refine (head_bound b hb a L ha).trans ?_
    have : (L : ℝ) ≤ K := by exact_mod_cast hLK
    nlinarith
  · push Not at hLK
    obtain ⟨L2, rfl⟩ : ∃ L2, L = K + L2 := ⟨L - K, by omega⟩
    rw [Finset.sum_range_add]
    refine (abs_add_le _ _).trans ?_
    have h1 := head_bound b hb a K ha
    have h2 := tail_abel b hb (by linarith) (a + K) L2 (by omega)
    have e : ∑ x ∈ Finset.range L2, Kb b ((a + (K + x) : ℕ) : ℤ) =
        ∑ i ∈ Finset.range L2, Kb b ((a + K + i : ℕ) : ℤ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_assoc]
    rw [e]
    have haK : 1 / b ≤ ((a + K : ℕ) : ℝ) := by push_cast; linarith [(show (1:ℝ) ≤ a by exact_mod_cast ha)]
    have h3 : 1 / (π * ((a + K : ℕ) : ℝ)) * (1 / (2 * b)) ≤ 1 := by
      have hpos : (0 : ℝ) < ((a + K : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) haK
      rw [div_mul_div_comm, one_mul, div_le_one (by positivity)]
      have : 1 ≤ b * ((a + K : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_left haK hb.le
        rwa [mul_one_div_cancel hb.ne'] at this
      nlinarith [Real.pi_gt_three]
    have h1' : (K : ℝ) * (2 * b) ≤ 3 := by nlinarith
    linarith

/-- PROVED. The sum of K_b over 0 to m - 1 is at most 5. -/
theorem prefix_bound (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1 / 4) (m : ℕ) :
    |∑ i ∈ Finset.range m, Kb b (i : ℤ)| ≤ 5 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h1 := pos_bound b hb hb' 1 m le_rfl
  have e : ∑ i ∈ Finset.range m, Kb b ((i + 1 : ℕ) : ℤ) =
      ∑ i ∈ Finset.range m, Kb b ((1 + i : ℕ) : ℤ) := by
    refine Finset.sum_congr rfl fun i _ => ?_; rw [Nat.add_comm]
  have h0 : |Kb b ((0 : ℕ) : ℤ)| ≤ 1 := by
    simp only [Nat.cast_zero, Kb_zero]
    rw [abs_le]; constructor <;> linarith
  rw [e]
  linarith [abs_add_le (∑ i ∈ Finset.range m, Kb b ((1 + i : ℕ) : ℤ)) (Kb b ((0 : ℕ) : ℤ))]

/-- PROVED. The sum of K_b over -m to -1 is at most 5, by evenness. -/
theorem neg_prefix_bound (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1 / 4) (m : ℕ) :
    |∑ i ∈ Finset.range m, Kb b (-((i : ℤ) + 1))| ≤ 5 := by
  have e : ∑ i ∈ Finset.range m, Kb b (-((i : ℤ) + 1)) =
      ∑ i ∈ Finset.range m, Kb b ((1 + i : ℕ) : ℤ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Kb_neg]; push_cast; ring_nf
  rw [e]; linarith [pos_bound b hb hb' 1 m le_rfl]

/-- PROVED. The sum of K_b over any integer run is at most 10, as a difference of two
values of the signed prefix sum. -/
theorem interval_sum_bound (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1 / 4) (A : ℤ) (L : ℕ) :
    |∑ i ∈ Finset.range L, Kb b (A + i)| ≤ 10 := by
  set F : ℤ → ℝ := fun n => if 0 ≤ n then ∑ i ∈ Finset.range n.toNat, Kb b (i : ℤ)
    else -∑ i ∈ Finset.range (-n).toNat, Kb b (-((i : ℤ) + 1)) with hF
  have hstep : ∀ n : ℤ, F (n + 1) - F n = Kb b n := by
    intro n
    rcases le_or_gt 0 n with hn | hn
    · have h1 : 0 ≤ n + 1 := by omega
      simp only [hF, if_pos hn, if_pos h1]
      rw [show (n + 1).toNat = n.toNat + 1 by omega, Finset.sum_range_succ]
      rw [Int.toNat_of_nonneg hn]; ring
    · rcases eq_or_lt_of_le (show n + 1 ≤ 0 by omega) with h0 | h0
      · have hn1 : n = -1 := by omega
        subst hn1
        simp [hF]
      · have h1 : ¬ 0 ≤ n + 1 := by omega
        have h2 : ¬ 0 ≤ n := by omega
        simp only [hF, if_neg h1, if_neg h2]
        rw [show (-n).toNat = (-(n + 1)).toNat + 1 by omega, Finset.sum_range_succ]
        have : -(((-(n + 1)).toNat : ℤ) + 1) = n := by omega
        rw [this]; ring
  have htel : ∀ L : ℕ, ∑ i ∈ Finset.range L, Kb b (A + i) = F (A + L) - F A := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih, ← hstep (A + L)]
      push_cast; ring_nf
  have hFb : ∀ n : ℤ, |F n| ≤ 5 := by
    intro n
    by_cases hn : 0 ≤ n
    · simp only [hF, if_pos hn]; exact prefix_bound b hb hb' _
    · simp only [hF, if_neg hn, abs_neg]; exact neg_prefix_bound b hb hb' _
  rw [htel]
  have := abs_sub (F (A + L)) (F A)
  linarith [hFb (A + L), hFb A]

/-- PROVED, formerly LEAF MEDIUM: P0088 page 7, the display before 27, kernel_Ico_sum_bound
near an edge, the O(1) part. For 0 < b at most 1/4 the sum of K_b over any integer interval is bounded by
an absolute constant. Proof sketch: K_b at 0 is 1 - 2b and K_b is even, so the sum is at
most 1 plus twice the largest partial sum of sin(2 pi k b)/(pi k) over a range of positive
k; for k at most 1/b use sin x at most x, beyond 1/b use Abel summation with
KernelSumPieces1122.abs_sum_sin_le and InnerWindowSplit1124.abel_antitone. -/
theorem kernel_Ico_uniform :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ (c : ℤ) (M1 M2 : ℕ),
      |∑ m ∈ Finset.Ico M1 M2, Kb b (c + (m : ℤ))| ≤ C1 := by
  refine ⟨10, by norm_num, ?_⟩
  intro b hb hb' c M1 M2
  rw [Finset.sum_Ico_eq_sum_range]
  have e : ∑ k ∈ Finset.range (M2 - M1), Kb b (c + ((M1 + k : ℕ) : ℤ)) =
      ∑ k ∈ Finset.range (M2 - M1), Kb b ((c + M1) + (k : ℤ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_; push_cast; ring_nf
  rw [e]
  exact interval_sum_bound b hb hb' (c + M1) (M2 - M1)

/-- LEAF: P0088 page 7, the display before 27, kernel_Ico_sum_bound away from the edges,
the O(1/(b d)) part. HARD. For 0 < b at most 1/4 the sum of K_b over the integers from
c + M1 to c + M2 - 1 is at most C2/(b (d + 1)), d the smaller of |c + M1| and |c + M2|.
Proof sketch: if 0 is outside the interval this is Abel summation of sin(2 pi k b) against
1/k with KernelSumPieces1122.abs_sum_sin_le; if 0 is inside, the sum over all integers is
1 - 2b minus the sawtooth series 2 times the sum over k at least 1 of sin(2 pi k b)/(pi k),
which is 0, so the sum is minus the two tails, each O(1/(b d)) by the same Abel step. -/
theorem kernel_Ico_far :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ (c : ℤ) (M1 M2 : ℕ),
      |∑ m ∈ Finset.Ico M1 M2, Kb b (c + (m : ℤ))| ≤
        C2 / (b * (min |(c : ℝ) + M1| |(c : ℝ) + M2| + 1)) := by
  sorry

/-- PROVED. A quantity bounded by C1 and by C2/x, x positive, is at most
(C1 + C2) min 1 (1/x). -/
theorem le_mul_min_of_two {S C1 C2 x : ℝ} (hx : 0 < x) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : S ≤ C1) (h2 : S ≤ C2 / x) : S ≤ (C1 + C2) * min 1 (1 / x) := by
  rcases le_total 1 (1 / x) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    have hx1 : 1 ≤ x := by
      rw [div_le_one hx] at h
      exact h
    have : C2 / x = C2 * (1 / x) := by ring
    have h3 : 0 ≤ C1 * (1 / x) := by positivity
    have h4 : S ≤ C2 * (1 / x) := this ▸ h2
    nlinarith [mul_nonneg hC1 (one_div_nonneg.mpr hx.le)]

/-- PROVED. The two pieces give the bound of kernel_Ico_sum_bound. -/
theorem kernel_Ico_sum_bound_of_pieces
    (hu : ∃ C1 : ℝ, 0 < C1 ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ (c : ℤ) (M1 M2 : ℕ),
      |∑ m ∈ Finset.Ico M1 M2, Kb b (c + (m : ℤ))| ≤ C1)
    (hf : ∃ C2 : ℝ, 0 < C2 ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ (c : ℤ) (M1 M2 : ℕ),
      |∑ m ∈ Finset.Ico M1 M2, Kb b (c + (m : ℤ))| ≤
        C2 / (b * (min |(c : ℝ) + M1| |(c : ℝ) + M2| + 1))) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ (c : ℤ) (M1 M2 : ℕ),
      |∑ m ∈ Finset.Ico M1 M2, Kb b (c + (m : ℤ))| ≤
        C0 * min 1 (1 / (b * (min |(c : ℝ) + M1| |(c : ℝ) + M2| + 1))) := by
  obtain ⟨C1, hC1, h1⟩ := hu
  obtain ⟨C2, hC2, h2⟩ := hf
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro b hb hb' c M1 M2
  have hd : 0 ≤ min |(c : ℝ) + M1| |(c : ℝ) + M2| :=
    le_min (abs_nonneg _) (abs_nonneg _)
  exact le_mul_min_of_two (by positivity) hC1.le hC2.le (h1 b hb hb' c M1 M2)
    (h2 b hb hb' c M1 M2)

/-- CONDITIONAL ON kernel_Ico_far: the exact type of
InnerWindowSplit1124.kernel_Ico_sum_bound. -/
theorem kernel_Ico_sum_bound_split :
    type_of% @LeanLab.KumchevLiu2007.InnerWindowSplit1124.kernel_Ico_sum_bound :=
  kernel_Ico_sum_bound_of_pieces kernel_Ico_uniform kernel_Ico_far

end LeanLab.KumchevLiu2007.KernelIcoSplit1124

#print axioms LeanLab.KumchevLiu2007.KernelIcoSplit1124.kernel_Ico_uniform
#print axioms LeanLab.KumchevLiu2007.KernelIcoSplit1124.interval_sum_bound
#print axioms LeanLab.KumchevLiu2007.KernelIcoSplit1124.le_mul_min_of_two
#print axioms LeanLab.KumchevLiu2007.KernelIcoSplit1124.kernel_Ico_sum_bound_of_pieces
#print axioms LeanLab.KumchevLiu2007.KernelIcoSplit1124.kernel_Ico_sum_bound_split
