/-
ROUTE BURST burst-20261122, session S111, STEP kernel-sum-split-p2. Further SPLIT of the two
MEDIUM LEAFs inner_window_bound and outer_square_bound of KernelSumSplit1122, P0088 Kumchev and
Liu 2007, page 7, the display before 27, used in page 9 display 27.
Inner window: write 1/log m1 as 1/log X plus the variation 1/log m1 - 1/log X. The first part is
the unweighted kernel window sum, LEAF kernel_window_sum MEDIUM, the sawtooth identity and the
Abel tails. The second part is LEAF weight_variation MEDIUM, the mean value bound for 1/log
times the harmonic sum of |K_b|. The range check of b and of the window, inner_ranges, is PROVED.
Outer sum: |f2Weight| at most 2 from KernelSumF2Bound1122 once z0 is in range, f2_ranges PROVED;
the harmonic sum over squares of the decay weight, LEAF edge_sum_bound MEDIUM; and the size of
the Y/X term, small_term PROVED.
inner_window_bound_twin and outer_square_bound_twin are PROVED from these leaves with the exact
types of the two leaves of KernelSumSplit1122, checked by type_of%.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelSumCount1122

namespace LeanLab.KumchevLiu2007.KernelSumSplitP2

open Real LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.KernelSumSplit1122
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 7, the display before 27, inner_window_bound, the unweighted kernel sum.
MEDIUM. For 0 < b at most 1/2 the sum of K_b over all integers vanishes, by the sawtooth
identity sum over k at least 1 of sin(2 pi k b)/k = pi(1 - 2b)/2, and Abel summation bounds
the tails beyond distance d by O(1/(b d)), while |sin x| at most |x| bounds all partial sums
by O(1). So the sum of K_b over the window [X - Y, X) shifted by m2^2 - n is O(edgeDecay). -/
theorem kernel_window_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 < b → b ≤ 1 / 2 → ∀ X Y : ℝ, 1 ≤ X - Y → ∀ n m2 : ℕ,
      |∑ m1 ∈ primeWindow X Y, Kb b (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ))| ≤
        C * edgeDecay X Y b n m2 := by
  sorry

/-- LEAF: P0088 page 7, the display before 27, inner_window_bound, partial summation in 1/log.
MEDIUM. For m1 in [X - Y, X), |1/log m1 - 1/log X| is O(Y/(X log^2 X)) by the mean value
theorem, and the sum of |K_b| over the window is at most 1 + (2/pi)(1 + log(Y + 1)) by
Kb_abs_le, so the variation part is O(Y/X). -/
theorem weight_variation :
    ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 → ∀ n m2 : ℕ,
        |∑ m1 ∈ primeWindow X (windowY X ε), (1 / Real.log (m1 : ℝ) - 1 / Real.log X) *
            Kb b (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ))| ≤ C * (windowY X ε / X) := by
  sorry

/-- PROVED: P0088 page 7, the display before 27, range checks for inner_window_bound.
With P = log^B X and Y = X^(7/12 + ε/2), Y at most X^(7/9), so for large X one has
0 < b = P^3/(q Y) at most 1/2, X - Y at least 1 and X at least 1. -/
theorem inner_ranges :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        0 < bq X ε B q ∧ bq X ε B q ≤ 1 / 2 ∧ 1 ≤ X - windowY X ε ∧ 1 ≤ X := by
  intro B hB ε hε hε'
  have h1 := (isLittleO_log_rpow_rpow_atTop (B * 3) (by norm_num : (0:ℝ) < 7 / 12)).bound
    (by norm_num : (0:ℝ) < 1 / 2)
  have h2 := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 2 / 9)).eventually_ge_atTop 2
  obtain ⟨X1, hX1⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨max X1 3, fun X hX q hq1 hqP => ?_⟩
  obtain ⟨hA, hBd⟩ := hX1 X (le_trans (le_max_left _ _) hX)
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  set Y := windowY X ε with hYdef
  set P := Real.log X ^ B with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hlog _
  have hY : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hbq : bq X ε B q = P ^ 3 / Y / q := by
    show (Y * P ^ (-2 : ℤ) / P)⁻¹ / (q : ℝ) = _
    rw [zpow_neg]
    field_simp
  have hP3 : P ^ 3 = Real.log X ^ (B * 3) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
    norm_num
  have hY7 : X ^ (7 / 12 : ℝ) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY9 : Y ≤ X ^ (7 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at hA
  refine ⟨?_, ?_, ?_, by linarith⟩
  · rw [hbq]; positivity
  · rw [hbq, div_div, div_le_iff₀ (by positivity), hP3]
    nlinarith [mul_nonneg (sub_nonneg.2 hq) hY.le]
  · have hsplit : X ^ (7 / 9 : ℝ) * X ^ (2 / 9 : ℝ) = X := by
      rw [← Real.rpow_add hX0]; norm_num
    have h79 : 0 ≤ X ^ (7 / 9 : ℝ) := Real.rpow_nonneg hX0.le _
    nlinarith [mul_nonneg (sub_nonneg.2 hBd) h79]

/-- PROVED from kernel_window_sum, weight_variation and inner_ranges: the exact type of
KernelSumSplit1122.inner_window_bound. -/
theorem inner_window_bound_twin : type_of% @KernelSumSplit1122.inner_window_bound := by
  intro B hB ε hε hε'
  obtain ⟨C1, hC1, hK⟩ := kernel_window_sum
  obtain ⟨C2, X2, hC2, hW⟩ := weight_variation ε hε hε'
  obtain ⟨X3, hR⟩ := inner_ranges B hB ε hε hε'
  refine ⟨C1 + C2, max X2 X3, by linarith, fun X hX q hq1 hqP n m2 _ => ?_⟩
  obtain ⟨hb0, hb2, hXY, hX1⟩ := hR X (le_trans (le_max_right _ _) hX) q hq1 hqP
  set Y := windowY X ε
  set b := bq X ε B q
  have hsplit : innerSum X Y b n m2 =
      1 / Real.log X * ∑ m1 ∈ primeWindow X Y, Kb b (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ)) +
        ∑ m1 ∈ primeWindow X Y, (1 / Real.log (m1 : ℝ) - 1 / Real.log X) *
            Kb b (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ)) := by
    rw [innerSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m1 _ => ?_
    ring
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hil : 0 ≤ 1 / Real.log X := div_nonneg zero_le_one hlog
  have he : 0 ≤ edgeDecay X Y b n m2 := KernelSumPieces1122.edgeDecay_nonneg X Y b n m2 hb0.le
  have hY : 0 ≤ Y / X := by
    have : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
    exact div_nonneg this (by linarith)
  have h1 := hK b hb0 hb2 X Y hXY n m2
  have h2 := hW X (le_trans (le_max_left _ _) hX) b hb0.le (by linarith) n m2
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hil]
  have h3 : 1 / Real.log X * |∑ m1 ∈ primeWindow X Y,
      Kb b (-(n : ℤ) + (m1 : ℤ) + ((m2 ^ 2 : ℕ) : ℤ))| ≤
      C1 * (edgeDecay X Y b n m2 / Real.log X) := by
    calc _ ≤ 1 / Real.log X * (C1 * edgeDecay X Y b n m2) := mul_le_mul_of_nonneg_left h1 hil
      _ = _ := by ring
  have h4 : 0 ≤ edgeDecay X Y b n m2 / Real.log X := div_nonneg he hlog
  nlinarith

/-- PROVED: P0088 page 7, the display before 27, range check of z0 for outer_square_bound.
For m2 in [Y^(1/2)/2, Y^(1/2)) one has sqrt m2 at least Y^(1/4)/sqrt 2, so
e at most z0 = Y^(1/4) P^(-2) at most sqrt m2 once P^2 at least sqrt 2 and Y^(1/4) at least
e P^2, true for large X. -/
theorem f2_ranges :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ∀ m2 ∈ squareWindow (windowY X ε),
        Real.exp 1 ≤ windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
          windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ Real.sqrt (m2 : ℝ) := by
  intro B hB ε hε hε'
  have h1 := (isLittleO_log_rpow_rpow_atTop (B * 2) (by norm_num : (0:ℝ) < 7 / 48)).bound
    (by norm_num : (0:ℝ) < 1 / 3)
  have h2 := (tendsto_rpow_atTop hB).eventually_ge_atTop 2
  have h3 := Real.tendsto_log_atTop.eventually (h2)
  obtain ⟨X1, hX1⟩ := eventually_atTop.1 (h1.and h3)
  refine ⟨max X1 3, fun X hX m2 hm2 => ?_⟩
  obtain ⟨hA, hP2⟩ := hX1 X (le_trans (le_max_left _ _) hX)
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  set Y := windowY X ε with hYdef
  set P := Real.log X ^ B with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hlog _
  have hY : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hP2' : (2 : ℝ) ≤ P := hP2
  have hz : Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) = Y ^ (1 / 4 : ℝ) / P ^ 2 := by
    rw [zpow_neg]; simp [div_eq_mul_inv]
  have hPsq : P ^ 2 = Real.log X ^ (B * 2) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
    norm_num
  have hY4 : X ^ (7 / 48 : ℝ) ≤ Y ^ (1 / 4 : ℝ) := by
    rw [hYdef, windowY, ← Real.rpow_mul hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at hA
  have hY4nn : 0 ≤ Y ^ (1 / 4 : ℝ) := Real.rpow_nonneg hY.le _
  rw [hz]
  constructor
  · rw [le_div_iff₀ (by positivity), hPsq]
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have hl0 : 0 ≤ Real.log X ^ (B * 2) := Real.rpow_nonneg hlog.le _
    nlinarith
  · -- m2 at least sqrt Y / 2, so sqrt m2 at least sqrt (sqrt Y / 2)
    have hm : Real.sqrt Y / 2 ≤ (m2 : ℝ) := (Finset.mem_filter.1 hm2).2.1
    have hsq : Real.sqrt Y = (Y ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hY.le]; norm_num
    have hlhs : 0 ≤ Y ^ (1 / 4 : ℝ) / P ^ 2 := by positivity
    rw [Real.le_sqrt hlhs (by positivity : (0:ℝ) ≤ m2)]
    have hP4 : (4 : ℝ) ≤ P ^ 2 := by nlinarith
    rw [div_pow]
    have hden : 0 < (P ^ 2) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have h16 : 16 ≤ (P ^ 2) ^ 2 := by nlinarith
    rw [hsq] at hm
    have hm0 : 0 ≤ (m2 : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h16 hm0]

/-- LEAF: P0088 page 7, the display before 27, outer_square_bound, the sum of the decay weight
over squares. MEDIUM. Squares near Y^(1/2) are spaced at least Y^(1/2) apart, sq_gap and
square_gap_window, so at most q Y^(1/2)/P^3 + 1 of them lie within 1/b of each edge,
card_squares_window, and the rest give a harmonic sum of size q Y^(1/2) log Y / P^3. With q at
most P and log Y at most log X this is O(Y^(1/2) P^(-2) log X). -/
theorem edge_sum_bound :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B → ∀ n : ℕ,
        ∑ m2 ∈ squareWindow (windowY X ε), edgeDecay X (windowY X ε) (bq X ε B q) n m2 ≤
          C * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-2 : ℤ) * Real.log X := by
  sorry

/-- PROVED: P0088 page 7, the display before 27, outer_square_bound, the Y/X term.
The window holds at most Y^(1/2) + 1 squares and Y/X at most X^(-2/9), so the term is at most
Y^(1/2) P^(-2) for large X. -/
theorem small_term :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ((squareWindow (windowY X ε)).card : ℝ) * (windowY X ε / X) ≤
        Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-2 : ℤ) := by
  intro B hB ε hε hε'
  have h1 := (isLittleO_log_rpow_rpow_atTop (B * 2) (by norm_num : (0:ℝ) < 2 / 9)).bound
    (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨X1, hX1⟩ := eventually_atTop.1 h1
  refine ⟨max X1 3, fun X hX => ?_⟩
  have hA := hX1 X (le_trans (le_max_left _ _) hX)
  have hX3 : 3 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  set Y := windowY X ε with hYdef
  set P := Real.log X ^ B with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hlog _
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by linarith) (by linarith)
  have hY9 : Y ≤ X ^ (7 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hPsq : P ^ 2 = Real.log X ^ (B * 2) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
    norm_num
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at hA
  have hsplit : X ^ (7 / 9 : ℝ) * X ^ (2 / 9 : ℝ) = X := by
    rw [← Real.rpow_add hX0]; norm_num
  have hcard : ((squareWindow Y).card : ℝ) ≤ Real.sqrt Y + 1 := by
    have h : (squareWindow Y).card ≤ ⌊Real.sqrt Y⌋₊ + 1 :=
      (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    have h' : ((squareWindow Y).card : ℝ) ≤ (⌊Real.sqrt Y⌋₊ : ℝ) + 1 := by exact_mod_cast h
    exact h'.trans (by linarith [Nat.floor_le (Real.sqrt_nonneg Y)])
  have hs1 : 1 ≤ Real.sqrt Y := by rw [Real.one_le_sqrt]; exact hY1
  have hz : P ^ (-2 : ℤ) = 1 / P ^ 2 := by rw [zpow_neg]; simp
  rw [hz]
  have hP2 : 0 < P ^ 2 := by positivity
  have h79 : 0 ≤ X ^ (7 / 9 : ℝ) := Real.rpow_nonneg hX0.le _
  have hl0 : 0 ≤ Real.log X ^ (B * 2) := Real.rpow_nonneg hlog.le _
  -- key: 2 * Y * P^2 ≤ X
  have hkey : 2 * Y * P ^ 2 ≤ X := by
    rw [hPsq]
    have : Y * Real.log X ^ (B * 2) ≤ X ^ (7 / 9 : ℝ) * (1 / 2 * X ^ (2 / 9 : ℝ)) :=
      mul_le_mul hY9 hA hl0 h79
    nlinarith
  have hYX : 0 ≤ Y / X := div_nonneg (by linarith) hX0.le
  calc ((squareWindow Y).card : ℝ) * (Y / X) ≤ (2 * Real.sqrt Y) * (Y / X) :=
        mul_le_mul_of_nonneg_right (by linarith) hYX
    _ = Real.sqrt Y * (2 * Y * P ^ 2 / X) / P ^ 2 := by field_simp
    _ ≤ Real.sqrt Y * 1 / P ^ 2 := by
        gcongr
        rw [div_le_one hX0]; exact hkey
    _ = Real.sqrt Y * (1 / P ^ 2) := by ring

/-- PROVED from f2_ranges, edge_sum_bound and small_term: the exact type of
KernelSumSplit1122.outer_square_bound. -/
theorem outer_square_bound_twin : type_of% @KernelSumSplit1122.outer_square_bound := by
  intro B hB ε hε hε' C hC
  obtain ⟨X1, hF⟩ := f2_ranges B hB ε hε hε'
  obtain ⟨C1, X2, hC1, hE⟩ := edge_sum_bound B hB ε hε hε'
  obtain ⟨X3, hS⟩ := small_term B hB ε hε hε'
  refine ⟨2 * C * (C1 + 1), max (max X1 X2) (max X3 2), by positivity,
    fun X hX q hq1 hqP n => ?_⟩
  have hX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX4 : 2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  set Y := windowY X ε
  set b := bq X ε B q
  set P := Real.log X ^ B
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hYnn : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
  have hPnn : 0 ≤ P := Real.rpow_nonneg hlog.le _
  have hb : 0 ≤ b := by
    show 0 ≤ (Y * P ^ (-2 : ℤ) / P)⁻¹ / (q : ℝ)
    have : 0 ≤ P ^ (-2 : ℤ) := zpow_nonneg hPnn _
    positivity
  have hYX : 0 ≤ Y / X := div_nonneg hYnn (by linarith)
  have hterm : ∀ m2 ∈ squareWindow Y,
      |f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m2 : ℝ)| *
        (C * (edgeDecay X Y b n m2 / Real.log X + Y / X)) ≤
      2 * C * (edgeDecay X Y b n m2 / Real.log X + Y / X) := by
    intro m2 hm2
    obtain ⟨hz1, hz2⟩ := hF X hX1 m2 hm2
    have hf := KernelSumF2Bound1122.abs_f2Weight_le_two _ _ hz1 hz2
    have he := KernelSumPieces1122.edgeDecay_nonneg X Y b n m2 hb
    have hnn : 0 ≤ C * (edgeDecay X Y b n m2 / Real.log X + Y / X) :=
      mul_nonneg hC.le (add_nonneg (div_nonneg he hlog.le) hYX)
    calc _ ≤ 2 * (C * (edgeDecay X Y b n m2 / Real.log X + Y / X)) :=
          mul_le_mul_of_nonneg_right hf hnn
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
    nsmul_eq_mul]
  have hE' := hE X hX2 q hq1 hqP n
  have hS' := hS X hX3
  have hEd : (∑ m2 ∈ squareWindow Y, edgeDecay X Y b n m2) / Real.log X ≤
      C1 * Real.sqrt Y * P ^ (-2 : ℤ) := by
    rw [div_le_iff₀ hlog]
    exact hE'
  have h2C : 0 ≤ 2 * C := by linarith
  calc 2 * C * ((∑ m2 ∈ squareWindow Y, edgeDecay X Y b n m2) / Real.log X +
        ((squareWindow Y).card : ℝ) * (Y / X)) ≤
      2 * C * (C1 * Real.sqrt Y * P ^ (-2 : ℤ) + Real.sqrt Y * P ^ (-2 : ℤ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hEd hS') h2C
    _ = 2 * C * (C1 + 1) * Real.sqrt Y * P ^ (-2 : ℤ) := by ring

end LeanLab.KumchevLiu2007.KernelSumSplitP2
