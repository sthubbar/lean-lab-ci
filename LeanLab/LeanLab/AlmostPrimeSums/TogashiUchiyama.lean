/-
AI-written Lean code, Claude, 2026-10-18, run 20261018T1002Z-987, unit U-0935.
P0072 Togashi and Uchiyama 1964, On the Representation of Large Even Integers as Sums of Two
Almost Primes. I, J. Fac. Sci. Hokkaido Univ. 18, pp. 60 to 68, read from the Hokkaido
repository scan, Sections 4 and 5, pp. 65 to 67.

The paper needs I(0) = 144 e^{2γ} ∫_2^{2.5} h(s) ds < 79.3025 with
h(s) = 1 / ((3 - s)((2s - 1)² - 2s² log s)).  It bounds the integral by convexity of h,
Lemma 6, and the values h(2) < 0.2895, h(2.3) < 0.3445, 0.4399 < h(2.5) < 0.4400.

PROVED here, zero sorry:
* `h2_lt`, `h23_lt`, `h25_bounds`: the three printed values of h.
* `lemma6_h1'''`, `lemma6_h1''`: the two sign facts the proof of Lemma 6 uses,
  12 log 2 - 8 > 0 and 18 log 2.5 - 21 < 0.
* `integral_h_lt`: ∫_2^{2.5} h < 0.1736, the paper's bound, by a different route: an upper
  Riemann sum over 200 pieces of width 1/400 with h bounded on each piece through
  monotone pieces of the formula, not by convexity. The true value is about 0.17056.
* `exp_two_gamma_lt`: e^{2γ} < 3.1723.
* `I0_lt`: 144 e^{2γ} ∫_2^{2.5} h < 79.3025, the paper's Section 4 conclusion in its s form.
* `section5_margin`: I(ε) < 79.3026 gives I(ε)/3 < 26.4342, and 26.4612 - 26.4342 > 0.0269.

* `I0_eq`, `I0_u_lt`: the substitution s = 3(1 - 1/u), so the paper's own
  I(0) = ∫_3^6 C_0(u)/u du < 79.3025.

Not proved: convexity of h itself, Lemma 6, which the Riemann sum route does not need, and
every analytic lemma, Sections 1 to 3, which stay cited. Goldbach is open.
-/
import Mathlib
import LeanLab.ChenExplicit.GammaBounds

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimeSums.TogashiUchiyama

/-- The paper's (2s - 1)² - 2s² log s. -/
def q (s : ℝ) : ℝ := (2 * s - 1) ^ 2 - 2 * s ^ 2 * log s

/-- The paper's h(s), Section 4. -/
def h (s : ℝ) : ℝ := 1 / ((3 - s) * q s)

/-! ### Logarithm bounds -/

/-- Upper bound polynomial for log(1 + y), 8 terms plus the geometric tail. -/
def Ur (y : ℝ) : ℝ :=
  y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 - y ^ 6 / 6 + y ^ 7 / 7 - y ^ 8 / 8
    + y ^ 9 / (1 - y)

def Uq (y : ℚ) : ℚ :=
  y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 - y ^ 6 / 6 + y ^ 7 / 7 - y ^ 8 / 8
    + y ^ 9 / (1 - y)

lemma Uq_cast (y : ℚ) : ((Uq y : ℚ) : ℝ) = Ur (y : ℝ) := by
  simp only [Uq, Ur]; push_cast; ring

lemma log_one_add_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) : log (1 + y) ≤ Ur y := by
  have hx : |(-y)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx 8
  rw [abs_le] at h
  simp only [sum_range_succ, sum_range_zero, abs_neg, abs_of_nonneg h0, sub_neg_eq_add] at h
  have h2 := h.2
  unfold Ur
  push_cast at h2
  nlinarith [h2]

/-- Lower bound for log(1 + y), 12 terms. -/
lemma log_one_add_ge {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 - y ^ 6 / 6 + y ^ 7 / 7 - y ^ 8 / 8
      + y ^ 9 / 9 - y ^ 10 / 10 + y ^ 11 / 11 - y ^ 12 / 12 - y ^ 13 / (1 - y) ≤ log (1 + y) := by
  have hx : |(-y)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; exact h1
  have h := Real.abs_log_sub_add_sum_range_le hx 12
  rw [abs_le] at h
  simp only [sum_range_succ, sum_range_zero, abs_neg, abs_of_nonneg h0, sub_neg_eq_add] at h
  have h2 := h.1
  push_cast at h2
  nlinarith [h2]

/-- log 2 < 0.6931471808, Mathlib. -/
lemma log_two_lt : log 2 < (6931471808 / 10 ^ 10 : ℝ) := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

lemma log_two_gt : (6931471803 / 10 ^ 10 : ℝ) < log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

/-- log b = log 2 + log (1 + (b - 2)/2). -/
lemma log_split {b : ℝ} (hb : 0 < b) : log b = log 2 + log (1 + (b - 2) / 2) := by
  rw [← log_mul (by norm_num) (by linarith)]; congr 1; ring

lemma log_le_of {b : ℝ} (h2 : 2 ≤ b) (h3 : b < 4) :
    log b ≤ 6931471808 / 10 ^ 10 + Ur ((b - 2) / 2) := by
  rw [log_split (by linarith)]
  have := log_one_add_le (y := (b - 2) / 2) (by linarith) (by linarith)
  linarith [log_two_lt]

/-! ### The three printed values of h -/

theorem h2_lt : h 2 < 0.2895 := by
  unfold h q
  have := log_two_lt
  have hd : (0 : ℝ) < (3 - 2) * ((2 * 2 - 1) ^ 2 - 2 * 2 ^ 2 * log 2) := by norm_num; linarith
  rw [div_lt_iff₀ hd]; norm_num; linarith

theorem h23_lt : h 2.3 < 0.3445 := by
  unfold h q
  have hl := log_le_of (b := 2.3) (by norm_num) (by norm_num)
  simp only [Ur] at hl; norm_num at hl
  have hd : (0 : ℝ) < (3 - 2.3) * ((2 * 2.3 - 1) ^ 2 - 2 * 2.3 ^ 2 * log 2.3) := by
    norm_num; linarith
  rw [div_lt_iff₀ hd]; norm_num; linarith

theorem h25_bounds : 0.4399 < h 2.5 ∧ h 2.5 < 0.4400 := by
  have hs := log_split (b := 2.5) (by norm_num)
  have hu := log_one_add_le (y := (2.5 - 2) / 2) (by norm_num) (by norm_num)
  have hlo := log_one_add_ge (y := (2.5 - 2) / 2) (by norm_num) (by norm_num)
  simp only [Ur] at hu
  norm_num at hu hlo hs
  have l1 := log_two_lt; have l2 := log_two_gt
  unfold h q
  have hd : (0 : ℝ) < (3 - 2.5) * ((2 * 2.5 - 1) ^ 2 - 2 * 2.5 ^ 2 * log 2.5) := by
    norm_num; linarith
  constructor
  · rw [lt_div_iff₀ hd]; norm_num; linarith
  · rw [div_lt_iff₀ hd]; norm_num; linarith

/-! ### Lemma 6, the two sign facts, and the trapezoid arithmetic -/

theorem lemma6_h1''' : 0 < 12 * log 2 - 8 := by have := log_two_gt; norm_num at this ⊢; linarith

theorem lemma6_h1'' : 18 * log 2.5 - 21 < 0 := by
  have hl := log_le_of (b := 2.5) (by norm_num) (by norm_num)
  simp only [Ur] at hl; norm_num at hl ⊢; linarith

/-- The paper's trapezoid arithmetic, p. 66, with the printed values. -/
theorem trapezoid_arith :
    (0.15 : ℝ) * (0.2895 + 0.3445) + 0.1 * (0.3445 + 0.4400) ≤ 0.09510 + 0.07845 ∧
    (0.09510 : ℝ) + 0.07845 < 0.1736 := by norm_num

/-! ### The integral, by an upper Riemann sum -/

/-- Piece bound: on [a, b] with 2 ≤ a ≤ b ≤ 2.5 and log b ≤ L, h ≤ 1 / ((3 - b)((2a-1)² - 2b²L)). -/
lemma h_le_on {a b L s : ℝ} (ha : 2 ≤ a) (hb : b ≤ 2.5) (hL : log b ≤ L)
    (hD : 0 < (3 - b) * ((2 * a - 1) ^ 2 - 2 * b ^ 2 * L)) (hs : s ∈ Set.Icc a b) :
    0 < (3 - s) * q s ∧ h s ≤ 1 / ((3 - b) * ((2 * a - 1) ^ 2 - 2 * b ^ 2 * L)) := by
  obtain ⟨hs1, hs2⟩ := hs
  have h3b : 0 < 3 - b := by linarith
  have hQ : 0 < (2 * a - 1) ^ 2 - 2 * b ^ 2 * L := by
    by_contra hc; push Not at hc; nlinarith
  have hlogs0 : 0 ≤ log s := log_nonneg (by linarith)
  have hlogs : log s ≤ log b := log_le_log (by linarith) hs2
  have hsq : (2 * a - 1) ^ 2 ≤ (2 * s - 1) ^ 2 := by nlinarith
  have hss : s ^ 2 ≤ b ^ 2 := by nlinarith
  have h1 : s ^ 2 * log s ≤ b ^ 2 * L := by
    calc s ^ 2 * log s ≤ b ^ 2 * log s := mul_le_mul_of_nonneg_right hss hlogs0
      _ ≤ b ^ 2 * L := mul_le_mul_of_nonneg_left (hlogs.trans hL) (by positivity)
  have hq : (2 * a - 1) ^ 2 - 2 * b ^ 2 * L ≤ q s := by unfold q; nlinarith
  have hden : (3 - b) * ((2 * a - 1) ^ 2 - 2 * b ^ 2 * L) ≤ (3 - s) * q s :=
    mul_le_mul (by linarith) hq hQ.le (by linarith)
  refine ⟨lt_of_lt_of_le hD hden, ?_⟩
  unfold h
  exact one_div_le_one_div_of_le hD hden

lemma h_contOn {a b L : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2.5) (hL : log b ≤ L)
    (hD : 0 < (3 - b) * ((2 * a - 1) ^ 2 - 2 * b ^ 2 * L)) : ContinuousOn h (Set.Icc a b) := by
  have hne : ∀ s ∈ Set.Icc a b, (3 - s) * q s ≠ 0 := fun s hs =>
    (h_le_on ha hb hL hD hs).1.ne'
  unfold h
  apply ContinuousOn.div continuousOn_const _ hne
  unfold q
  apply ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
  apply ContinuousOn.sub (by fun_prop)
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.log continuousOn_id
  intro s hs; exact ne_of_gt (by simp at hs ⊢; linarith [hs.1])

lemma integral_piece {a b L c : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2.5) (hL : log b ≤ L)
    (hD : 0 < (3 - b) * ((2 * a - 1) ^ 2 - 2 * b ^ 2 * L))
    (hc : b - a ≤ c * ((3 - b) * ((2 * a - 1) ^ 2 - 2 * b ^ 2 * L))) :
    ∫ s in a..b, h s ≤ c := by
  set M := 1 / ((3 - b) * ((2 * a - 1) ^ 2 - 2 * b ^ 2 * L))
  have hint : IntervalIntegrable h MeasureTheory.volume a b :=
    (h_contOn ha hab hb hL hD).intervalIntegrable_of_Icc hab
  have h1 : ∫ s in a..b, h s ≤ ∫ s in a..b, M :=
    intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
      (fun s hs => (h_le_on ha hb hL hD hs).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  have h2 : (b - a) * M ≤ c := by
    simp only [M]; rw [← div_eq_mul_one_div, div_le_iff₀ hD]; exact hc
  linarith

/-! ### The 200 pieces, checked over ℚ by the kernel -/

def cs : List ℕ := [730491169, 731031151, 731579480, 732136189, 732701314, 733274889, 733856953, 734447540, 735046689, 735654436, 736270822, 736895885, 737529664, 738172199, 738823532, 739483704, 740152757, 740830734, 741517677, 742213632, 742918642, 743632753, 744356010, 745088461, 745830152, 746581131, 747341448, 748111151, 748890290, 749678916, 750477080, 751284836, 752102235, 752929331, 753766178, 754612833, 755469350, 756335787, 757212200, 758098650, 758995193, 759901891, 760818805, 761745995, 762683525, 763631457, 764589857, 765558789, 766538319, 767528514, 768529442, 769541172, 770563774, 771597318, 772641875, 773697520, 774764325, 775842364, 776931715, 778032453, 779144656, 780268403, 781403775, 782550851, 783709715, 784880449, 786063139, 787257869, 788464726, 789683799, 790915177, 792158950, 793415209, 794684048, 795965561, 797259843, 798566992, 799887105, 801220282, 802566624, 803926233, 805299213, 806685670, 808085709, 809499440, 810926971, 812368414, 813823882, 815293490, 816777352, 818275587, 819788314, 821315654, 822857730, 824414665, 825986587, 827573622, 829175902, 830793557, 832426721, 834075530, 835740120, 837420632, 839117207, 840829987, 842559119, 844304750, 846067029, 847846110, 849642145, 851455292, 853285709, 855133557, 856998999, 858882202, 860783333, 862702564, 864640067, 866596019, 868570598, 870563986, 872576366, 874607926, 876658854, 878729343, 880819589, 882929789, 885060146, 887210864, 889382150, 891574216, 893787275, 896021544, 898277246, 900554603, 902853844, 905175199, 907518905, 909885200, 912274326, 914686529, 917122061, 919581174, 922064129, 924571187, 927102615, 929658684, 932239670, 934845854, 937477519, 940134955, 942818456, 945528322, 948264856, 951028368, 953819171, 956637586, 959483937, 962358555, 965261775, 968193941, 971155399, 974146503, 977167614, 980219096, 983301323, 986414673, 989559532, 992736293, 995945354, 999187122, 1002462012, 1005770443, 1009112844, 1012489653, 1015901313, 1019348276, 1022831003, 1026349964, 1029905636, 1033498506, 1037129069, 1040797830, 1044505304, 1048252015, 1052038496, 1055865293, 1059732959, 1063642059, 1067593171, 1071586880, 1075623786, 1079704500, 1083829642, 1087999849, 1092215766, 1096478055, 1100787389, 1105144454, 1109549951]

def pa (i : ℕ) : ℚ := 2 + (i : ℚ) / 400
def Lq (i : ℕ) : ℚ := 6931471808 / 10 ^ 10 + Uq ((pa (i + 1) - 2) / 2)
def Dq (i : ℕ) : ℚ := (3 - pa (i + 1)) * ((2 * pa i - 1) ^ 2 - 2 * pa (i + 1) ^ 2 * Lq i)
def cq (i : ℕ) : ℚ := (cs.getD i 0 : ℚ) / 10 ^ 12

def okPiece (i : ℕ) : Bool := decide (0 < Dq i) && decide (pa (i + 1) - pa i ≤ cq i * Dq i)

def allOk : ℕ → Bool
  | 0 => true
  | n + 1 => allOk n && okPiece n

def sumc : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumc n + cq n

theorem allOk_200 : allOk 200 = true := by decide +kernel

theorem sumc_200 : sumc 200 ≤ 1736 / 10000 := by decide +kernel

lemma okPiece_of_allOk {n i : ℕ} (h : allOk n = true) (hi : i < n) : okPiece i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allOk, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ih h.1 hi
    · subst hi; exact h.2

lemma sum_eq_sumc (n : ℕ) : ∑ i ∈ range n, ((cq i : ℚ) : ℝ) = ((sumc n : ℚ) : ℝ) := by
  induction n with
  | zero => simp [sumc]
  | succ n ih => rw [sum_range_succ, ih, sumc]; push_cast; ring

def pr (i : ℕ) : ℝ := ((pa i : ℚ) : ℝ)

lemma pr_eq (i : ℕ) : pr i = 2 + (i : ℝ) / 400 := by simp [pr, pa]

lemma piece_bound {i : ℕ} (hi : i < 200) : ∫ s in pr i..pr (i + 1), h s ≤ ((cq i : ℚ) : ℝ) := by
  have hok := okPiece_of_allOk allOk_200 hi
  simp only [okPiece, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hD, hc⟩ := hok
  have hiR : (i : ℝ) + 1 ≤ 200 := by exact_mod_cast hi
  have ha : 2 ≤ pr i := by
    rw [pr_eq]; have : (0 : ℝ) ≤ (i : ℝ) / 400 := by positivity
    linarith
  have hab : pr i ≤ pr (i + 1) := by rw [pr_eq, pr_eq]; push_cast; linarith
  have hb : pr (i + 1) ≤ 2.5 := by rw [pr_eq]; push_cast; norm_num; linarith
  have hL : log (pr (i + 1)) ≤ ((Lq i : ℚ) : ℝ) := by
    have := log_le_of (b := pr (i + 1)) (by linarith) (by linarith)
    simp only [Lq]; push_cast; rw [Uq_cast]; push_cast
    simpa [pr] using this
  apply integral_piece ha hab hb hL
  · have := (Rat.cast_lt (K := ℝ)).mpr hD
    simpa [Dq, pr] using this
  · have := (Rat.cast_le (K := ℝ)).mpr hc
    simpa [Dq, pr] using this

/-- **The integral bound of Section 4**: ∫_2^{2.5} h < 0.1736. -/
theorem integral_h_lt : ∫ s in (2 : ℝ)..2.5, h s < 0.1736 := by
  have hint : ∀ k < 200, IntervalIntegrable h MeasureTheory.volume (pr k) (pr (k + 1)) := by
    intro k hk
    have hok := okPiece_of_allOk allOk_200 hk
    simp only [okPiece, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hkR : (k : ℝ) + 1 ≤ 200 := by exact_mod_cast hk
    have ha : 2 ≤ pr k := by
      rw [pr_eq]; have : (0 : ℝ) ≤ (k : ℝ) / 400 := by positivity
      linarith
    have hab : pr k ≤ pr (k + 1) := by rw [pr_eq, pr_eq]; push_cast; linarith
    have hb : pr (k + 1) ≤ 2.5 := by rw [pr_eq]; push_cast; norm_num; linarith
    have hL : log (pr (k + 1)) ≤ ((Lq k : ℚ) : ℝ) := by
      have := log_le_of (b := pr (k + 1)) (by linarith) (by linarith)
      simp only [Lq]; push_cast; rw [Uq_cast]; push_cast
      simpa [pr] using this
    have hD : 0 < (3 - pr (k + 1)) * ((2 * pr k - 1) ^ 2 - 2 * pr (k + 1) ^ 2 * ((Lq k : ℚ) : ℝ)) := by
      have := (Rat.cast_lt (K := ℝ)).mpr hok.1
      simpa [Dq, pr] using this
    exact (h_contOn ha hab hb hL hD).intervalIntegrable_of_Icc hab
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have e0 : pr 0 = 2 := by simp [pr, pa]
  have e200 : pr 200 = 2.5 := by simp [pr, pa]; norm_num
  rw [e0, e200] at hsum
  rw [← hsum]
  have hle : ∑ k ∈ range 200, ∫ s in pr k..pr (k + 1), h s ≤
      ∑ k ∈ range 200, ((cq k : ℚ) : ℝ) :=
    sum_le_sum fun k hk => piece_bound (mem_range.mp hk)
  rw [sum_eq_sumc] at hle
  have hs := (Rat.cast_le (K := ℝ)).mpr sumc_200
  have : ((1736 / 10000 : ℚ) : ℝ) < 0.1736 + 1e-12 := by norm_num
  have h1 : ((1736 / 10000 : ℚ) : ℝ) = 0.1736 := by norm_num
  rw [h1] at hs
  -- the piece sum is at most 0.1723, strictly below 0.1736
  have hstrict : sumc 200 < 1736 / 10000 := by decide +kernel
  have hs' := (Rat.cast_lt (K := ℝ)).mpr hstrict
  rw [h1] at hs'
  linarith

/-! ### e^{2γ} and the Section 4 conclusion -/

theorem exp_two_gamma_lt : exp (2 * eulerMascheroniConstant) < 3.1723 := by
  have hg := LeanLab.ChenExplicit.Gamma.gamma_lt
  have h1 : exp (0.57722 : ℝ) ≤ 1.7810802 := by
    have h := Real.exp_bound' (x := (0.57722 : ℝ)) (by norm_num) (by norm_num) (n := 14) (by norm_num)
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h; linarith
  have h2 : exp (2 * eulerMascheroniConstant) < exp (0.57722 : ℝ) * exp 0.57722 := by
    rw [← exp_add]; exact exp_lt_exp.mpr (by linarith)
  have h3 : exp (0.57722 : ℝ) * exp 0.57722 ≤ 1.7810802 * 1.7810802 :=
    mul_le_mul h1 h1 (exp_pos _).le (by norm_num)
  have : (1.7810802 : ℝ) * 1.7810802 < 3.1723 := by norm_num
  linarith

/-- **Section 4 conclusion**, s form: I(0) = 144 e^{2γ} ∫_2^{2.5} h < 79.3025. -/
theorem I0_lt : 144 * exp (2 * eulerMascheroniConstant) * ∫ s in (2 : ℝ)..2.5, h s < 79.3025 := by
  have hI := integral_h_lt
  have hE := exp_two_gamma_lt
  have hE0 := exp_pos (2 * eulerMascheroniConstant)
  rcases le_or_gt 0 (∫ s in (2 : ℝ)..2.5, h s) with h0 | h0
  · have : exp (2 * eulerMascheroniConstant) * ∫ s in (2 : ℝ)..2.5, h s ≤ 3.1723 * 0.1736 := by
      apply mul_le_mul hE.le hI.le h0 (by norm_num)
    nlinarith
  · nlinarith [mul_neg_of_pos_of_neg hE0 h0]

/-! ### The u form: the paper's I(0) = ∫_3^6 C_0(u)/u du, by the substitution s = 3(1 - 1/u) -/

/-- The denominator of h is positive on all of [2, 2.5], from the 200 kernel-checked pieces. -/
lemma den_pos {s : ℝ} (hs : s ∈ Set.Icc (2 : ℝ) 2.5) : 0 < (3 - s) * q s := by
  obtain ⟨h1, h2⟩ := hs
  set i := min (Nat.floor ((s - 2) * 400)) 199 with hi
  have hi200 : i < 200 := by omega
  have hok := okPiece_of_allOk allOk_200 hi200
  simp only [okPiece, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hiR : (i : ℝ) + 1 ≤ 200 := by exact_mod_cast hi200
  have hlo : pr i ≤ s := by
    rw [pr_eq]
    have hf : ((Nat.floor ((s - 2) * 400) : ℕ) : ℝ) ≤ (s - 2) * 400 :=
      Nat.floor_le (by nlinarith)
    have : (i : ℝ) ≤ (Nat.floor ((s - 2) * 400) : ℕ) := by exact_mod_cast min_le_left _ _
    linarith
  have hhi : s ≤ pr (i + 1) := by
    rw [pr_eq]; push_cast
    rcases le_or_gt (Nat.floor ((s - 2) * 400)) 199 with hc | hc
    · have hii : i = Nat.floor ((s - 2) * 400) := by omega
      have := Nat.lt_floor_add_one ((s - 2) * 400)
      rw [hii]; linarith
    · have hii : i = 199 := by omega
      rw [hii]; norm_num; linarith
  have ha : 2 ≤ pr i := by
    rw [pr_eq]; have : (0 : ℝ) ≤ (i : ℝ) / 400 := by positivity
    linarith
  have hb : pr (i + 1) ≤ 2.5 := by rw [pr_eq]; push_cast; norm_num; linarith
  have hL : log (pr (i + 1)) ≤ ((Lq i : ℚ) : ℝ) := by
    have := log_le_of (b := pr (i + 1)) (by linarith) (by linarith)
    simp only [Lq]; push_cast; rw [Uq_cast]; push_cast
    simpa [pr] using this
  have hD : 0 < (3 - pr (i + 1)) * ((2 * pr i - 1) ^ 2 - 2 * pr (i + 1) ^ 2 * ((Lq i : ℚ) : ℝ)) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hok.1
    simpa [Dq, pr] using this
  exact (h_le_on ha hb hL hD ⟨hlo, hhi⟩).1

lemma h_cont : ContinuousOn h (Set.Icc (2 : ℝ) 2.5) := by
  have hne : ∀ s ∈ Set.Icc (2 : ℝ) 2.5, (3 - s) * q s ≠ 0 := fun s hs => (den_pos hs).ne'
  unfold h
  apply ContinuousOn.div continuousOn_const _ hne
  unfold q
  apply ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
  apply ContinuousOn.sub (by fun_prop)
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.log continuousOn_id
  intro s hs; exact ne_of_gt (by simp at hs ⊢; linarith [hs.1])

/-- The substitution, s = 3(1 - 1/u). -/
def sub (u : ℝ) : ℝ := 3 * (1 - 1 / u)

/-- The paper's C_ε(u) at ε = 0 on 3 ≤ u ≤ 6, where a = 3(1 - 1/u) lies in [2, 2.5], so the
second case of its definition applies: C_0(u) = 144 e^{2C} / ((2a - 1)² - 2a² log a). -/
def C0 (u : ℝ) : ℝ := 144 * exp (2 * eulerMascheroniConstant) / q (sub u)

/-- The paper's I(0) = ∫_3^6 C_0(u)/u du equals 144 e^{2γ} ∫_2^{2.5} h(s) ds. -/
theorem I0_eq : ∫ u in (3 : ℝ)..6, C0 u / u =
    144 * exp (2 * eulerMascheroniConstant) * ∫ s in (2 : ℝ)..2.5, h s := by
  have hsub3 : sub 3 = 2 := by norm_num [sub]
  have hsub6 : sub 6 = 2.5 := by norm_num [sub]
  have hcomp := intervalIntegral.integral_comp_mul_deriv'' (a := (3 : ℝ)) (b := 6) (f := sub)
    (f' := fun u => 3 / u ^ 2) (g := h)
    (by
      unfold sub
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro x hx; rw [Set.uIcc_of_le (by norm_num)] at hx; simp at hx ⊢; linarith [hx.1])
    (by
      intro x hx
      simp only [min_eq_left (show (3 : ℝ) ≤ 6 by norm_num),
        max_eq_right (show (3 : ℝ) ≤ 6 by norm_num), Set.mem_Ioo] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      apply HasDerivAt.hasDerivWithinAt
      unfold sub
      have h1 : HasDerivAt (fun u : ℝ => 1 / u) (-(x ^ 2)⁻¹) x := by
        simpa [one_div] using hasDerivAt_inv hx0
      have := ((hasDerivAt_const x (1 : ℝ)).sub h1).const_mul 3
      convert this using 1; field_simp; ring)
    (by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx; rw [Set.uIcc_of_le (by norm_num)] at hx; simp at hx
      have : 3 ≤ x := hx.1; positivity)
    (by
      apply h_cont.mono
      rintro _ ⟨x, hx, rfl⟩
      rw [Set.uIcc_of_le (by norm_num)] at hx
      obtain ⟨h3, h6⟩ := hx
      unfold sub
      have hx0 : 0 < x := by linarith
      constructor
      · rw [show (2 : ℝ) = 3 * (1 - 1 / 3) by norm_num]
        have : 1 / x ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
        linarith
      · rw [show (2.5 : ℝ) = 3 * (1 - 1 / 6) by norm_num]
        have : 1 / 6 ≤ 1 / x := one_div_le_one_div_of_le hx0 h6
        linarith)
  rw [hsub3, hsub6] at hcomp
  rw [← hcomp, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by norm_num)] at hu
  obtain ⟨h3, h6⟩ := hu
  have hu0 : u ≠ 0 := by linarith
  have h3s : 3 - sub u = 3 / u := by unfold sub; field_simp; ring
  simp only [Function.comp, C0, h, h3s]
  have hq : q (sub u) ≠ 0 := by
    have hs : sub u ∈ Set.Icc (2 : ℝ) 2.5 := by
      unfold sub
      have hx0 : 0 < u := by linarith
      constructor
      · rw [show (2 : ℝ) = 3 * (1 - 1 / 3) by norm_num]
        have : 1 / u ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
        linarith
      · rw [show (2.5 : ℝ) = 3 * (1 - 1 / 6) by norm_num]
        have : 1 / 6 ≤ 1 / u := one_div_le_one_div_of_le hx0 h6
        linarith
    have := den_pos hs
    rw [h3s] at this
    intro h0; rw [h0, mul_zero] at this; exact lt_irrefl _ this
  field_simp

/-- **Section 4 conclusion in the paper's own u form**: I(0) = ∫_3^6 C_0(u)/u du < 79.3025. -/
theorem I0_u_lt : ∫ u in (3 : ℝ)..6, C0 u / u < 79.3025 := by
  rw [I0_eq]; exact I0_lt

/-- **Section 5 arithmetic**, p. 67: from I(ε) < 79.3026, I(ε)/3 < 26.4342, and
26.4612 - 26.4342 > 0.0269. -/
theorem section5_margin :
    (∀ I : ℝ, I < 79.3026 → I / 3 < 26.4342) ∧ (0.0269 : ℝ) < 26.4612 - 26.4342 := by
  refine ⟨fun I hI => by linarith, by norm_num⟩

end LeanLab.AlmostPrimeSums.TogashiUchiyama
