import LeanLab.HelfgottMajor.BookZeroHonest1123
import Mathlib

/-!
# Zeta case of book display 3.95 from Bellotti and Wong, burst-20261122, session S116

Bellotti and Wong, Improved estimates for the argument and zero-counting function of the
Riemann zeta-function, arXiv 2412.15470v2, accepted by Math. Comp., Theorem 1.1, page 1,
second bound, checked on the page image: for every T at least e, the absolute value of
N of T minus T over 2 pi times log of T over 2 pi e is at most
0.11200 log T + 0.12567 log log T + 3.77417, where N of T counts the zeros with 0 < Re < 1 and
0 < Im at most T, with full weight at height T.

This covers log T from about 20.2 on, so with line 1 of book display 3.63 up to log T = 25.5 it
gives the trivial character case of display 3.95 WITHOUT `BookZeroHonest1123.zeta_window`, which
has no source, and without `BookZeroHonest1123.zeta_362_hsw`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.BookZeroBW1123
open LeanLab.HelfgottMajor.ZeroCount1623 LeanLab.HelfgottMajor.BookZeroSplit1122
open LeanLab.HelfgottMajor.BookZeroHonest1123
open Complex Set Filter Topology

/-- The main term alone fits the Bellotti and Wong error bound between e and 2 pi e. -/
lemma bw_main_term_le_error_in_band {T : ℝ} (hT : Real.exp 1 ≤ T)
    (hb : T ≤ 2 * Real.pi * Real.exp 1) :
    |T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
      0.112 * Real.log T + 0.12567 * Real.log (Real.log T) + 3.77417 := by
  have hlog : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hT
  have hT1 : 1 ≤ T := (by linarith [Real.exp_one_gt_d9] : (1 : ℝ) ≤ Real.exp 1).trans hT
  have hloglog := Real.log_nonneg hlog
  obtain ⟨hlo, hhi⟩ := bookMain_one_band hT1 hb
  simp only [bookMain, Nat.cast_one, one_mul] at hlo hhi
  rw [abs_le]
  constructor <;> linarith

/-- LEAF: Bellotti and Wong, arXiv 2412.15470v2, Theorem 1.1, page 1, second bound, T at
least e. Class HARD, citation wall, a printed theorem resting on a computer check.
COUNT TAKEN: the paper's N of T, zeros of zeta, here the L function of chi modulo 1, with
0 < Re s < 1 and 0 < Im s at most T, FULL weight at Im s = T, with multiplicity.
Main term T over 2 pi times log of T over 2 pi e. -/
theorem bw_count (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : Real.exp 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im), (mult χ ρ : ℝ)) -
      T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        0.112 * Real.log T + 0.12567 * Real.log (Real.log T) + 3.77417 := by
  rcases le_or_gt T 14.13 with hlo | hhi
  · have hN : (∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im),
        (mult χ ρ : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun ρ hρ => ?_
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
      obtain ⟨⟨hz, hre0, hre1, him⟩, _⟩ := hρ
      rw [DirichletCharacter.LFunction_modOne_eq] at hz
      have hfirst := zeta_first_zero hz hre0 hre1
      exfalso
      linarith
    have hb : T ≤ 2 * Real.pi * Real.exp 1 := by
      have hpi := Real.pi_gt_three
      have he := Real.exp_one_gt_d9
      nlinarith
    rw [hN, zero_sub, abs_neg]
    exact bw_main_term_le_error_in_band hT hb
  · sorry

lemma bookMain_one_eq (T : ℝ) :
    bookMain 1 T = T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) := by
  simp [bookMain]

/-- The book count from the full weight count of `bw_count`, PROVED from `bw_count` and the
kept LEAF `BookZeroSplit1122.zeta_first_zero`, which rules out zeros at height 0. The upper side
is `bw_count` at T, the lower side `bw_count` just below T and the left limit.
COUNT: the ONE SIDED book count, half weight at the ends. -/
theorem bw_book (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 14.13 ≤ T) :
    |bookCount χ T - bookMain 1 T| ≤
      0.112 * Real.log T + 0.12567 * Real.log (Real.log T) + 3.77417 := by
  have he := Real.exp_one_lt_d9
  have heT : Real.exp 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  set F := (stripZeros_finite χ T).toFinset with hF
  have hnz : ∀ ρ ∈ F, ρ.im ≠ 0 := by
    intro ρ hρ h
    have hρ' := (stripZeros_finite χ T).mem_toFinset.mp hρ
    have hz := hρ'.1
    rw [DirichletCharacter.LFunction_modOne_eq] at hz
    have := zeta_first_zero hz hρ'.2.1 hρ'.2.2.1
    rw [h, abs_zero] at this
    linarith
  set N := ∑ ρ ∈ F.filter (fun ρ => 0 < ρ.im), (mult χ ρ : ℝ) with hN
  set M := ∑ ρ ∈ F.filter (fun ρ => |ρ.im| < T ∧ 0 < ρ.im), (mult χ ρ : ℝ) with hM
  have hB : bookCount χ T = ∑ ρ ∈ F, if 0 ≤ ρ.im then halfWeight T ρ.im * (mult χ ρ : ℝ) else 0 := by
    unfold bookCount; rw [Finset.sum_filter]
  have hBN : bookCount χ T ≤ N := by
    rw [hB, hN, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hm : (0 : ℝ) ≤ mult χ ρ := Nat.cast_nonneg _
    have h0 := hnz ρ hρ
    unfold halfWeight
    split_ifs <;> first | linarith | (exfalso; tauto) | (exfalso; apply h0; linarith)
  have hMB : M ≤ bookCount χ T := by
    rw [hB, hM, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hm : (0 : ℝ) ≤ mult χ ρ := Nat.cast_nonneg _
    unfold halfWeight
    split_ifs with h1 h2 h3 <;> first | linarith | skip
    all_goals
      (exfalso; obtain ⟨ha, hb⟩ := h1; rcases h3 with h3 | h3 <;>
          [linarith; (rw [abs_of_pos hb, h3] at ha; linarith)])
  have hup := (abs_le.mp (bw_count χ heT.le)).2
  obtain ⟨ε, hε, hgap⟩ := left_gap χ T
  set g : ℝ → ℝ := fun t ↦ t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1)) -
    (0.112 * Real.log t + 0.12567 * Real.log (Real.log t) + 3.77417) with hg
  have hev : ∀ᶠ t in 𝓝[<] T, g t ≤ M := by
    have hlt : max (T - ε) (Real.exp 1) < T := max_lt (by linarith) heT
    filter_upwards [Ioo_mem_nhdsLT hlt] with t ht
    have het : Real.exp 1 ≤ t := (lt_of_le_of_lt (le_max_right _ _) ht.1).le
    have hTe : T - ε < t := lt_of_le_of_lt (le_max_left _ _) ht.1
    have he' := hgap t hTe ht.2
    have hb := (abs_le.mp (bw_count χ het)).1
    rw [he', Finset.filter_filter] at hb
    simp only [hg]
    linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hcont : ContinuousAt g T := by
    have h1 : ContinuousAt (fun t ↦ t / (2 * Real.pi) *
        Real.log (t / (2 * Real.pi * Real.exp 1))) T :=
      ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) (by positivity))
    have h2 : ContinuousAt (fun t ↦ Real.log t) T := Real.continuousAt_log hT0.ne'
    have h3 : ContinuousAt (fun t ↦ Real.log (Real.log t)) T :=
      ContinuousAt.log h2 hlogT.ne'
    exact h1.sub (((continuousAt_const.mul h2).add (continuousAt_const.mul h3)).add
      continuousAt_const)
  have hlim : Tendsto g (𝓝[<] T) (𝓝 (g T)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlow : g T ≤ M := le_of_tendsto hlim hev
  simp only [hg] at hlow
  rw [bookMain_one_eq, abs_le]
  constructor <;> linarith

/-- The trivial character case of display 3.95, PROVED from `zeta_first_zero`,
`zeta_362_363_first` and `bw_count`, cuts at T = 14.13 and log T = 25.5.
It never uses `zeta_window`, `zeta_362_hsw` or `zeta_362_363_second`. -/
theorem zeta_case_bw (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain 1 T| ≤ bookError 1 T := by
  have hpi := Real.pi_gt_three
  have he := Real.exp_one_gt_d9
  have hErr : bookError 1 T = 0.15 * Real.log T + 3.389 := by
    simp only [bookError, Nat.cast_one, one_mul]
  rw [hErr]
  rcases le_or_gt T 14.13 with hlo | hhi
  · have hN : bookCount χ T = 0 := by
      unfold bookCount
      refine Finset.sum_eq_zero fun ρ hρ => ?_
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
      simp only [stripZeros, Set.mem_ofPred_eq] at hρ
      obtain ⟨⟨hz, hre0, hre1, him⟩, _⟩ := hρ
      rw [DirichletCharacter.LFunction_modOne_eq] at hz
      have := zeta_first_zero hz hre0 hre1
      exfalso; linarith
    have hb : T ≤ 2 * Real.pi * Real.exp 1 := by nlinarith
    obtain ⟨m1, m2⟩ := bookMain_one_band hT hb
    have hL := Real.log_nonneg hT
    rw [hN, abs_le]
    constructor <;> linarith
  · have hT14 : (14.13 : ℝ) ≤ T := hhi.le
    have hTpos : 0 < T := by linarith
    have t1 : 5 / (48 * Real.pi * T) ≤ 0.00246 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have t2 : 0.068 / T ^ 3 ≤ 0.00004 := by
      rw [div_le_iff₀ (by positivity)]
      have : (14.13 : ℝ) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ (by norm_num) hT14 3
      nlinarith
    have t1' : 0 ≤ 5 / (48 * Real.pi * T) := by positivity
    have t2' : 0 ≤ 0.068 / T ^ 3 := by positivity
    have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT
    rcases le_or_gt (Real.log T) 25.5 with hs | hl
    · obtain ⟨a1, a2⟩ := abs_le.mp (zeta_362_363_first χ hT14)
      rw [abs_le]
      constructor <;> linarith
    · obtain ⟨a1, a2⟩ := abs_le.mp (bw_book χ hT14)
      have hLpos : 0 < Real.log T := by linarith
      have hdiv := Real.log_le_sub_one_of_pos (x := Real.log T / 25.5) (by positivity)
      rw [Real.log_div hLpos.ne' (by norm_num)] at hdiv
      have h255 := log_25_5_le
      have h' : Real.log T / 25.5 = Real.log T * (2 / 51) := by
        rw [div_eq_mul_inv]; norm_num
      rw [h'] at hdiv
      have hlogL : Real.log (Real.log T) ≤ 2.25 + Real.log T * (2 / 51) := by linarith
      have hlogL0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg (by linarith)
      rw [abs_le]
      constructor <;> linarith

/-- ASSEMBLY. Exactly the sealed statement `ZeroCount1623.book_zero_count`. CONDITIONAL ON
`bmor_two_sided`, `book_395_complex`, `zeta_first_zero`, `zeta_362_363_first` and `bw_count`.
No LEAF without a printed source except the footnote 5 wall `book_395_complex`. -/
theorem book_zero_count_bw {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  by_cases h1 : χ = 1
  · have hq : q = 1 := by
      have h := (DirichletCharacter.isPrimitive_def χ).mp hχ
      rw [h1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hq
    exact zeta_case_bw χ hT
  · by_cases hr : χ⁻¹ = χ
    · exact real_case χ hχ hr h1 hT
    · exact book_395_complex χ hχ hr hT

example : type_of% @book_zero_count_bw = type_of% @ZeroCount1623.book_zero_count := rfl

/-- `MainHyps123.BookZeroCount` from the same LEAFs as `book_zero_count_bw`. -/
theorem book_zero_count_bw_named : MainHyps123.BookZeroCount :=
  fun _ _ χ hχ _ hT => book_zero_count_bw χ hχ hT

/-- Twin of `ZeroCount1623.zero_count_two_sided`. For q above 1 CONDITIONAL ON
`bmor_two_sided` alone; for q = 1 on `zeta_first_zero`, `zeta_362_363_first` and `bw_count`. -/
theorem zero_count_two_sided_bw {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) - 2 * bookMain q T| ≤
      2 * bookError q T := by
  rcases Nat.lt_or_ge 1 q with hq | hq
  · exact zero_count_two_sided_bmor χ hχ hq hT
  · have h0 := NeZero.pos q
    obtain rfl : q = 1 := by omega
    exact two_sided_of_one_sided χ hT fun t ht => ⟨zeta_case_bw χ ht, zeta_case_bw χ⁻¹ ht⟩

example : type_of% @zero_count_two_sided_bw = type_of% @ZeroCount1623.zero_count_two_sided :=
  rfl

end LeanLab.HelfgottMajor.BookZeroBW1123
