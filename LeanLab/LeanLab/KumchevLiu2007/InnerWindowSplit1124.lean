/-
ROUTE BURST burst-20261124, session S1, unit S1-01, route of Task628.major_arc_block.
SPLIT of the LEAF KernelSumSplit1122.inner_window_bound, P0088 Kumchev and Liu 2007,
page 7, the display before 27, through bound27 of the major arc route.

The inner sum over the integer window [X - Y, X) of 1/log m1 times K_b(m1 + m2^2 - n)
is treated by partial summation in the weight 1/log m1, exactly the proof sketch in the
doc comment of inner_window_bound. The pieces:
1. window_eq_Ico, PROVED: the window is the integer interval from ceil(X - Y) to ceil X.
2. abel_antitone, PROVED: Abel summation with a nonnegative decreasing weight.
3. decay_compare, PROVED: moving the two window edges by at most one costs a factor 2.
4. kernel_Ico_sum_bound, LEAF MEDIUM: the sum of K_b over an integer interval is O(1),
   and O(1/(b d)) at distance d of 0 from the interval ends; the sawtooth series.
5. log_weight_bounds, PROVED, formerly LEAF EASY: 1/log m on the window is at most 2/log X and varies by
   at most Y/X, and Y is at most X, for X large.
6. bq_small, PROVED, formerly LEAF EASY: 0 < b = P^3/(qY) at most 1/4 for X large.
inner_window_bound_of_pieces proves the exact type of inner_window_bound from them;
inner_window_bound_split is CONDITIONAL ON kernel_Ico_sum_bound only.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelSumPieces1122

namespace LeanLab.KumchevLiu2007.InnerWindowSplit1124

open Real LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.KernelSumSplit1122 LeanLab.KumchevLiu2007.KernelSumPieces1122
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- PROVED. Page 2 display 5: the integer window X - Y at most m below X is the
interval from ceil(X - Y) to ceil X. -/
theorem window_eq_Ico (X Y : ℝ) :
    primeWindow X Y = Finset.Ico ⌈X - Y⌉₊ ⌈X⌉₊ := by
  ext m
  simp only [primeWindow, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
    Nat.ceil_le, Nat.lt_ceil]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor h2.le), h1, h2⟩

/-- PROVED. Abel summation identity behind the display before 27, in range form. -/
theorem abel_identity (w f : ℕ → ℝ) (M N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), w (M + i) * f (M + i) =
      w (M + N) * ∑ i ∈ Finset.range (N + 1), f (M + i) +
        ∑ k ∈ Finset.range N, (w (M + k) - w (M + (k + 1))) *
          ∑ i ∈ Finset.range (k + 1), f (M + i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ (fun i => w (M + i) * f (M + i)), ih,
      Finset.sum_range_succ (fun k => (w (M + k) - w (M + (k + 1))) *
        ∑ i ∈ Finset.range (k + 1), f (M + i)) N,
      Finset.sum_range_succ (fun i => f (M + i)) (N + 1)]
    ring

/-- PROVED. Abel summation with a nonnegative decreasing weight: the weighted sum is
at most the last weight times the full sum plus the total drop of the weight times a
bound for all partial sums. -/
theorem abel_antitone (w f : ℕ → ℝ) (M N : ℕ) (S : ℝ)
    (hw : ∀ i j : ℕ, i ≤ j → j ≤ N → w (M + j) ≤ w (M + i))
    (hpart : ∀ k : ℕ, k ≤ N → |∑ i ∈ Finset.range (k + 1), f (M + i)| ≤ S) :
    |∑ i ∈ Finset.range (N + 1), w (M + i) * f (M + i)| ≤
      |w (M + N)| * |∑ i ∈ Finset.range (N + 1), f (M + i)| +
        (w M - w (M + N)) * S := by
  rw [abel_identity]
  refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hdrop : ∀ k ∈ Finset.range N,
      |(w (M + k) - w (M + (k + 1))) * ∑ i ∈ Finset.range (k + 1), f (M + i)| ≤
        (w (M + k) - w (M + (k + 1))) * S := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have h0 : 0 ≤ w (M + k) - w (M + (k + 1)) :=
      sub_nonneg.mpr (hw k (k + 1) (by omega) (by omega))
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (hpart k (by omega)) h0
  refine (Finset.sum_le_sum hdrop).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, Finset.sum_range_sub' (fun k => w (M + k)) N]
  simp

/-- PROVED. Moving each of the two edges by at most one changes the decay weight
min 1 (1/(b (d + 1))) by at most a factor 2, for 0 < b at most 1/2. -/
theorem decay_compare (u u' r r' b : ℝ) (hb : 0 < b) (hb' : b ≤ 1 / 2)
    (hu : |u - r| ≤ 1) (hu' : |u' - r'| ≤ 1) :
    min 1 (1 / (b * (min |u| |u'| + 1))) ≤ 2 * min 1 (1 / (b * (min |r| |r'| + 1))) := by
  set d := min |r| |r'| with hd
  set e := min |u| |u'| with he
  have hd0 : 0 ≤ d := le_min (abs_nonneg _) (abs_nonneg _)
  have he0 : 0 ≤ e := le_min (abs_nonneg _) (abs_nonneg _)
  have hed : d - 1 ≤ e := by
    have h1 : |r| - 1 ≤ |u| := by
      have := abs_sub_abs_le_abs_sub r u
      rw [abs_sub_comm] at this; linarith
    have h2 : |r'| - 1 ≤ |u'| := by
      have := abs_sub_abs_le_abs_sub r' u'
      rw [abs_sub_comm] at this; linarith
    rcases min_choice |u| |u'| with h | h <;> rw [he, h]
    · linarith [min_le_left |r| |r'|]
    · linarith [min_le_right |r| |r'|]
  by_cases hd1 : d ≤ 1
  · have : 1 ≤ 1 / (b * (d + 1)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    rw [min_eq_left this]
    linarith [min_le_left 1 (1 / (b * (e + 1)))]
  · push_neg at hd1
    have hkey : 1 / (b * (e + 1)) ≤ 2 * (1 / (b * (d + 1))) := by
      rw [div_le_iff₀ (by positivity)]
      have : 2 * (1 / (b * (d + 1))) * (b * (e + 1)) = 2 * (e + 1) / (d + 1) := by
        field_simp
      rw [this, le_div_iff₀ (by positivity)]
      linarith
    rcases le_total 1 (1 / (b * (d + 1))) with h | h
    · rw [min_eq_left h]; linarith [min_le_left 1 (1 / (b * (e + 1)))]
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans hkey

/-- LEAF: P0088 page 7, the display before 27, inner_window_bound step 1, the kernel over
an integer interval. MEDIUM. For 0 < b at most 1/4 and integers c, M1, M2 the sum of K_b
at c + m over M1 at most m below M2 is at most C0 times min 1 (1/(b (d + 1))), where d is
the smaller of |c + M1| and |c + M2|. Proof sketch: the sum of K_b over all integers is 1 - 2b
minus the sawtooth series 2 times the sum over k at least 1 of sin(2 pi k b)/(pi k), which is
1 - 2b, so it vanishes; partial sums of sin(2 pi k b) are at most 1/(2b), see
KernelSumPieces1122.abs_sum_sin_le, so Abel summation bounds every tail from distance d by
O(1/(b d)); and the partial sums of sin(2 pi k b)/(pi k) are uniformly bounded, which gives
O(1) near an edge. -/
theorem kernel_Ico_sum_bound :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ (c : ℤ) (M1 M2 : ℕ),
      |∑ m ∈ Finset.Ico M1 M2, Kb b (c + (m : ℤ))| ≤
        C0 * min 1 (1 / (b * (min |(c : ℝ) + M1| |(c : ℝ) + M2| + 1))) := by
  sorry

/-- PROVED. Page 16 parameters: Y = X^(7/12 + eps/2) is at most X/2 for X at least 2^9
and eps at most 7/18. -/
theorem windowY_le_half (ε : ℝ) (hε' : ε ≤ 7 / 18) : ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
    windowY X ε ≤ X / 2 := by
  refine ⟨2 ^ (9 : ℝ), by norm_num, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := le_trans (by norm_num) hX
  have hX0 : 0 < X := by linarith
  unfold windowY
  have h1 : X ^ (7 / 12 + ε / 2) ≤ X ^ (7 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have h2 : (2 : ℝ) ≤ X ^ (2 / 9 : ℝ) := by
    have : (2 ^ (9 : ℝ)) ^ (2 / 9 : ℝ) ≤ X ^ (2 / 9 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hX (by norm_num)
    rw [← Real.rpow_mul (by norm_num)] at this
    norm_num at this
    linarith
  have h3 : X ^ (7 / 9 : ℝ) * X ^ (2 / 9 : ℝ) = X := by
    rw [← Real.rpow_add hX0]; norm_num
  have h4 : 0 ≤ X ^ (7 / 9 : ℝ) := by positivity
  nlinarith

/-- PROVED, formerly LEAF EASY: P0088 page 7, the display before 27, inner_window_bound
step 2, the weight f1 of page 15 on the window. With Y = X^(7/12 + eps/2), eps at most 7/18, for X large Y is
at most X, every m of the window [X - Y, X) has 0 at most 1/log m at most 2/log X, and
1/log m decreases on the window with total variation at most 1/log(X - Y) - 1/log X, which
is at most Y/X. -/
theorem log_weight_bounds :
    ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      windowY X ε ≤ X ∧
      ∀ m m' : ℕ, m ∈ primeWindow X (windowY X ε) → m' ∈ primeWindow X (windowY X ε) →
        m ≤ m' →
        0 ≤ 1 / Real.log (m' : ℝ) ∧ 1 / Real.log (m' : ℝ) ≤ 1 / Real.log (m : ℝ) ∧
        1 / Real.log (m : ℝ) ≤ 2 / Real.log X ∧
        1 / Real.log (m : ℝ) - 1 / Real.log (m' : ℝ) ≤ windowY X ε / X := by
  intro ε hε hε'
  obtain ⟨X1, hX1, hY⟩ := windowY_le_half ε hε'
  refine ⟨max X1 (2 * Real.exp 2), le_trans hX1 (le_max_left _ _), fun X hX => ?_⟩
  have hYX := hY X (le_trans (le_max_left _ _) hX)
  have he : 2 * Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hexp : 0 < Real.exp 2 := Real.exp_pos 2
  have hX0 : 0 < X := by linarith
  have hYnn : 0 ≤ windowY X ε := by unfold windowY; positivity
  refine ⟨by linarith, fun m m' hm hm' hmm => ?_⟩
  simp only [primeWindow, Finset.mem_filter] at hm hm'
  obtain ⟨_, hm1, hm2⟩ := hm
  obtain ⟨_, hm1', hm2'⟩ := hm'
  have hmX : X / 2 ≤ (m : ℝ) := by linarith
  have hmm' : (m : ℝ) ≤ m' := by exact_mod_cast hmm
  have hhalf : Real.exp 2 ≤ X / 2 := by linarith
  have hm0 : 0 < (m : ℝ) := by linarith
  have hlogm : 2 ≤ Real.log (m : ℝ) := by
    rw [Real.le_log_iff_exp_le hm0]; linarith
  have hlogm' : Real.log (m : ℝ) ≤ Real.log (m' : ℝ) := Real.log_le_log hm0 hmm'
  have hlogX2 : Real.log X - Real.log 2 ≤ Real.log (m : ℝ) := by
    rw [← Real.log_div hX0.ne' (by norm_num)]
    exact Real.log_le_log (by positivity) hmX
  have hlX : 2 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; linarith
  have hlog2 : Real.log 2 ≤ Real.log X / 2 := by
    have h1 := hlX
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by linarith) hlogm'
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  · have hdiff : Real.log (m' : ℝ) - Real.log (m : ℝ) ≤ 2 * windowY X ε / X := by
      rw [← Real.log_div (by linarith) hm0.ne']
      refine (Real.log_le_sub_one_of_pos (div_pos (by linarith) hm0)).trans ?_
      rw [div_sub_one hm0.ne', div_le_div_iff₀ hm0 hX0]
      nlinarith
    have hprod : 2 ≤ Real.log (m : ℝ) * Real.log (m' : ℝ) := by nlinarith
    have hd2 : (Real.log (m' : ℝ) - Real.log (m : ℝ)) * X ≤ 2 * windowY X ε := by
      rwa [le_div_iff₀ hX0] at hdiff
    rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by nlinarith) hX0]
    nlinarith

/-- PROVED, formerly LEAF EASY: P0088 page 4 display 14 and page 7, the scale b = P^3/(q Y)
of the display before 27. With P = (log X)^B and q from 1 to P, b is positive and at most 1/4 for X large,
since Y = X^(7/12 + eps/2) beats every power of log X. -/
theorem bq_small :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → 0 < bq X ε B q ∧ bq X ε B q ≤ 1 / 4 := by
  intro B hB ε hε hε'
  have ht := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1 / 12)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X1, h1⟩ := Filter.eventually_atTop.mp ht
  refine ⟨max (2 ^ (12 : ℝ)) X1, fun X hX q hq => ?_⟩
  have hXb : 2 ^ (12 : ℝ) ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le (by norm_num) hXb
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  set P := Real.log X ^ B with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hL B
  have hY : 0 < windowY X ε := by unfold windowY; positivity
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hbq : bq X ε B q = P ^ 3 / windowY X ε / q := by
    unfold bq
    rw [zpow_neg, zpow_ofNat]
    field_simp
    rfl
  rw [hbq]
  refine ⟨by positivity, ?_⟩
  have h := h1 X (le_trans (le_max_right _ _) hX)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hP,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at h
  have hP3 : P ^ 3 ≤ X ^ (1 / 4 : ℝ) := by
    calc P ^ 3 ≤ (X ^ (1 / 12 : ℝ)) ^ 3 := pow_le_pow_left₀ hP.le h 3
      _ = X ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hYl : 4 * X ^ (1 / 4 : ℝ) ≤ windowY X ε := by
    unfold windowY
    have e1 : X ^ (7 / 12 : ℝ) ≤ X ^ (7 / 12 + ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
    have e2 : (4 : ℝ) ≤ X ^ (1 / 3 : ℝ) := by
      have : (2 ^ (12 : ℝ)) ^ (1 / 3 : ℝ) ≤ X ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hXb (by norm_num)
      rw [← Real.rpow_mul (by norm_num)] at this
      norm_num at this
      linarith
    have e3 : X ^ (1 / 4 : ℝ) * X ^ (1 / 3 : ℝ) = X ^ (7 / 12 : ℝ) := by
      rw [← Real.rpow_add hX0]; norm_num
    have e4 : 0 ≤ X ^ (1 / 4 : ℝ) := by positivity
    nlinarith
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- PROVED from the pieces above: the exact type of KernelSumSplit1122.inner_window_bound.
Its hypotheses are the three pieces; two of them are now PROVED. -/
theorem inner_window_bound_of_pieces
    (hK : ∃ C0 : ℝ, 0 < C0 ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ (c : ℤ) (M1 M2 : ℕ),
      |∑ m ∈ Finset.Ico M1 M2, Kb b (c + (m : ℤ))| ≤
        C0 * min 1 (1 / (b * (min |(c : ℝ) + M1| |(c : ℝ) + M2| + 1))))
    (hW : ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      windowY X ε ≤ X ∧
      ∀ m m' : ℕ, m ∈ primeWindow X (windowY X ε) → m' ∈ primeWindow X (windowY X ε) →
        m ≤ m' →
        0 ≤ 1 / Real.log (m' : ℝ) ∧ 1 / Real.log (m' : ℝ) ≤ 1 / Real.log (m : ℝ) ∧
        1 / Real.log (m : ℝ) ≤ 2 / Real.log X ∧
        1 / Real.log (m : ℝ) - 1 / Real.log (m' : ℝ) ≤ windowY X ε / X)
    (hb : ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → 0 < bq X ε B q ∧ bq X ε B q ≤ 1 / 4) :
    type_of% @inner_window_bound := by
  intro B hB ε hε hε'
  obtain ⟨C0, hC0, hKb⟩ := hK
  obtain ⟨X1, hX1, hWX⟩ := hW ε hε hε'
  obtain ⟨X2, hbX⟩ := hb B hB ε hε hε'
  refine ⟨4 * C0, max X1 X2, by positivity, fun X hX q hq1 _ n m2 _ => ?_⟩
  have hXX1 : X1 ≤ X := le_trans (le_max_left _ _) hX
  have hXX2 : X2 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 ≤ X := zero_le_one.trans (hX1.trans hXX1)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (hX1.trans hXX1)
  obtain ⟨hYX, hlog⟩ := hWX X hXX1
  obtain ⟨hb0, hb4⟩ := hbX X hXX2 q hq1
  set Y := windowY X ε with hYdef
  set b := bq X ε B q with hbdef
  set c : ℤ := -(n : ℤ) + ((m2 ^ 2 : ℕ) : ℤ) with hc
  set M1 := ⌈X - Y⌉₊ with hM1
  set M2 := ⌈X⌉₊ with hM2
  have hED : 0 ≤ edgeDecay X Y b n m2 := edgeDecay_nonneg X Y b n m2 hb0.le
  have hYX0 : 0 ≤ Y / X := div_nonneg (by rw [hYdef]; unfold windowY; positivity) hX0
  have hinner : innerSum X Y b n m2 =
      ∑ m ∈ Finset.Ico M1 M2, 1 / Real.log (m : ℝ) * Kb b (c + (m : ℤ)) := by
    rw [innerSum, window_eq_Ico]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 2
    rw [hc]; ring
  -- the decay of the full window sum
  have hdec : min 1 (1 / (b * (min |(c : ℝ) + M1| |(c : ℝ) + M2| + 1))) ≤
      2 * edgeDecay X Y b n m2 := by
    unfold edgeDecay
    have hcR : (c : ℝ) = -(n : ℝ) + (m2 : ℝ) ^ 2 := by rw [hc]; push_cast; ring
    have e1 : |(n : ℝ) - (m2 : ℝ) ^ 2 - (X - Y)| = |(c : ℝ) + (X - Y)| := by
      rw [hcR, ← abs_neg]; ring_nf
    have e2 : |(n : ℝ) - (m2 : ℝ) ^ 2 - X| = |(c : ℝ) + X| := by
      rw [hcR, ← abs_neg]; ring_nf
    rw [e1, e2]
    apply decay_compare _ _ _ _ b hb0 (by linarith)
    · have h1 : X - Y ≤ (M1 : ℝ) := Nat.le_ceil _
      have h2 : (M1 : ℝ) < X - Y + 1 := Nat.ceil_lt_add_one (by linarith)
      rw [abs_le]; constructor <;> linarith
    · have h1 : X ≤ (M2 : ℝ) := Nat.le_ceil _
      have h2 : (M2 : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0
      rw [abs_le]; constructor <;> linarith
  rw [hinner]
  rcases Nat.lt_or_ge M1 M2 with hlt | hge
  swap
  · rw [Finset.Ico_eq_empty_of_le hge, Finset.sum_empty, abs_zero]
    positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, M2 = M1 + (N + 1) := ⟨M2 - M1 - 1, by omega⟩
  have hmem : ∀ i : ℕ, i ≤ N → M1 + i ∈ primeWindow X Y := by
    intro i hi
    rw [window_eq_Ico, Finset.mem_Ico]
    omega
  have hsumR : ∀ g : ℕ → ℝ, ∑ m ∈ Finset.Ico M1 M2, g m =
      ∑ i ∈ Finset.range (N + 1), g (M1 + i) := by
    intro g
    rw [Finset.sum_Ico_eq_sum_range, hN, Nat.add_sub_cancel_left]
  have hpartK : ∀ k : ℕ, |∑ i ∈ Finset.range (k + 1), Kb b (c + ((M1 + i : ℕ) : ℤ))| ≤ C0 := by
    intro k
    have h := hKb b hb0 hb4 c M1 (M1 + (k + 1))
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at h
    refine h.trans ?_
    calc C0 * min 1 _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hC0.le
      _ = C0 := mul_one C0
  have hfull : |∑ i ∈ Finset.range (N + 1), Kb b (c + ((M1 + i : ℕ) : ℤ))| ≤
      C0 * (2 * edgeDecay X Y b n m2) := by
    have h := hKb b hb0 hb4 c M1 M2
    rw [hsumR (fun m => Kb b (c + (m : ℤ)))] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdec hC0.le)
  rw [hsumR (fun m => 1 / Real.log (m : ℝ) * Kb b (c + (m : ℤ)))]
  have hab := abel_antitone (fun m => 1 / Real.log (m : ℝ)) (fun m => Kb b (c + (m : ℤ)))
    M1 N C0 (fun i j hij hjN => (hlog (M1 + i) (M1 + j) (hmem i (hij.trans hjN))
      (hmem j hjN) (by omega)).2.1) (fun k _ => hpartK k)
  have hlast := hlog M1 (M1 + N) (hmem 0 (Nat.zero_le _)) (hmem N le_rfl) (by omega)
  obtain ⟨hw0, _, _, hvar⟩ := hlast
  have hwN : 1 / Real.log ((M1 + N : ℕ) : ℝ) ≤ 2 / Real.log X :=
    (hlog (M1 + N) (M1 + N) (hmem N le_rfl) (hmem N le_rfl) le_rfl).2.2.1
  refine hab.trans ?_
  rw [abs_of_nonneg hw0]
  have hlX : 0 ≤ 2 / Real.log X := hw0.trans hwN
  calc 1 / Real.log ((M1 + N : ℕ) : ℝ) *
        |∑ i ∈ Finset.range (N + 1), Kb b (c + ((M1 + i : ℕ) : ℤ))| +
        (1 / Real.log (M1 : ℝ) - 1 / Real.log ((M1 + N : ℕ) : ℝ)) * C0
      ≤ 2 / Real.log X * (C0 * (2 * edgeDecay X Y b n m2)) + Y / X * C0 := by
        exact add_le_add (mul_le_mul hwN hfull (abs_nonneg _) hlX)
          (mul_le_mul_of_nonneg_right hvar hC0.le)
    _ = 4 * C0 * (edgeDecay X Y b n m2 / Real.log X + Y / X) - 3 * C0 * (Y / X) := by
        ring
    _ ≤ 4 * C0 * (edgeDecay X Y b n m2 / Real.log X + Y / X) := by
        have : 0 ≤ 3 * C0 * (Y / X) := by positivity
        linarith

/-- An example checks the assembly has the type of the parent leaf. -/
example (hK : ∃ C0 : ℝ, 0 < C0 ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 4 → ∀ (c : ℤ) (M1 M2 : ℕ),
      |∑ m ∈ Finset.Ico M1 M2, Kb b (c + (m : ℤ))| ≤
        C0 * min 1 (1 / (b * (min |(c : ℝ) + M1| |(c : ℝ) + M2| + 1)))) :
    type_of% @inner_window_bound :=
  inner_window_bound_of_pieces hK log_weight_bounds bq_small

/-- The parent leaf, CONDITIONAL ON kernel_Ico_sum_bound only. -/
theorem inner_window_bound_split : type_of% @inner_window_bound :=
  inner_window_bound_of_pieces kernel_Ico_sum_bound log_weight_bounds bq_small

end LeanLab.KumchevLiu2007.InnerWindowSplit1124

#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.window_eq_Ico
#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.abel_identity
#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.abel_antitone
#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.decay_compare
#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.windowY_le_half
#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.log_weight_bounds
#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.bq_small
#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.inner_window_bound_of_pieces
#print axioms LeanLab.KumchevLiu2007.InnerWindowSplit1124.inner_window_bound_split
