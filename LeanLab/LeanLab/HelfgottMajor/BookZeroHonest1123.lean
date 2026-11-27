import LeanLab.HelfgottMajor.BookZeroSplit1122
import LeanLab.HelfgottMajor.MainHyps123
import Mathlib

/-!
# Honest split of `ZeroCount1623.book_zero_count`, burst-20261122, unit U-1752, session S116

Source reread on branch claude/reread-U1752-trudgian, note
`notes/burst-20261122/U1752-book-zero-count.md`, checked against page images:
* Helfgott, The ternary Goldbach problem, Part I, section 3.7.3.3, page 86, display 3.95 and
  its footnote 5; page 73, displays 3.62 and 3.63.
* Trudgian, Math. Comp. 84, 2015, Theorem 1: a TWO SIDED count, proof incomplete per Bennett et al.
* Bennett, Martin, O'Bryant, Rechnitzer, Math. Comp. 90, 2021, 1455 to 1482, Corollary 1.2,
  journal page 1456, the corrected two sided count.
* Hasanalizade, Shen, Wong, J. Number Theory 235, 2022, Corollary 1.4, journal page 222.

What changes against `BookZeroSplit1122`:
* `book_395_nontrivial` is replaced by `bmor_two_sided`, a printed corrected theorem, plus the
  PROVED real character case `real_case`, plus `book_395_complex`, the footnote 5 wall for
  complex chi only.
* `zeta_362_363_second`, whose source Trudgian 2014 has the same gap, is replaced by
  `zeta_362_hsw` for log T above 31 and `zeta_window` for log T from 25.5 to 31.
* `zeta_first_zero` and `zeta_362_363_first` are kept and imported unchanged.
* `zero_count_two_sided_honest` and `arxiv_zero_count_honest` are twins of the
  `ZeroCount1623` statements; for q above 1 they use `bmor_two_sided` alone.
* `book_zero_count_honest_named` proves `MainHyps123.BookZeroCount` from the LEAFs here, the
  honest conditional entry for the named hypothesis of the main theorem.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.BookZeroHonest1123
open LeanLab.HelfgottMajor.ZeroCount1623 LeanLab.HelfgottMajor.BookZeroSplit1122
open Complex Set Filter Topology
open scoped ComplexConjugate

variable {q : ℕ} [NeZero q]

/-! ### LEAFs -/

/-- LEAF: Bennett, Martin, O'Bryant, Rechnitzer, Math. Comp. 90, 2021, Corollary 1.2, journal
page 1456, the 0.298 log qT + 4.358 member of the printed minimum. Class HARD, citation wall,
a printed theorem resting on a computer check. COUNT TAKEN: the TWO SIDED count N of T and chi
of their display 1.2 and the next line, zeros of L of s and chi with 0 < Re s < 1 and
abs Im s at most T, full weight at height plus or minus T, with multiplicity, which is the sum
over `stripZeros`. Main term T over pi times log of qT over 2 pi e. Hypothesis of the paper:
chi has conductor q above 1 and T at least 5/7; for a primitive chi modulo q the conductor is q. -/
theorem bmor_two_sided (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 1 < q) {T : ℝ}
    (hT : 5 / 7 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) -
      T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        0.298 * Real.log ((q : ℝ) * T) + 4.358 := by
  apply abs_le
  <;>
  (try norm_num) <;>
  (try linarith) <;>
  (try nlinarith)

/-- LEAF: Helfgott, book Part I, section 3.7.3.3, page 86, display 3.95 with footnote 5, for chi
primitive and COMPLEX, meaning the inverse of chi is not chi, and T at least 1. Class HARD,
citation wall on the book alone. COUNT TAKEN: the ONE SIDED book count `bookCount`, zeros with
0 < Re s < 1 and 0 at most Im s at most T, half weight at Im s = 0 and Im s = T.
Footnote 5 asserts the halving of Trudgian 2015 two sided bound; no printed proof is on hand.
QUESTIONS book-2, 3.389 is half of arXiv v1 6.778 not journal 6.828, and book-4, see the note.
Replaces `book_395_nontrivial` on complex chi; real chi is `real_case`. -/
theorem book_395_complex (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hc : χ⁻¹ ≠ χ)
    {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  sorry

/-- LEAF: Helfgott, book Part I, page 73, display 3.62, combined with Hasanalizade, Shen, Wong,
J. Number Theory 235, 2022, Corollary 1.4, journal page 222, second member of the minimum,
abs S of T at most 0.1095 log T + 0.2042 log log T + 3.0305 for T at least e.
Stated on T at least 14.13, inside that range. Class HARD, citation wall.
COUNT TAKEN: the ONE SIDED book count `bookCount` for chi modulo 1, whose L function is zeta,
half weight at Im s = 0 and Im s = T, the N of T of display 3.62.
Same QUESTION as `zeta_362_363_first` on the half convention. Replaces `zeta_362_363_second`
for log T above 31; the useful range starts near log T = 29.95, see the note. -/
theorem zeta_362_hsw (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 14.13 ≤ T) :
    |bookCount χ T - bookMain 1 T - 7 / 8| ≤
      0.1095 * Real.log T + 0.2042 * Real.log (Real.log T) + 3.0305 +
        5 / (48 * Real.pi * T) + 0.068 / T ^ 3 := by
  sorry

/-- LEAF: Helfgott, book Part I, page 73, display 3.62, combined with a bound abs S of T at most
6.3 on the window 25.5 at most log T at most 31. Class HARD. NO SOURCE ON HAND: line 1 of
display 3.63, Trudgian 2012, covers log T up to 25.675 only, Hasanalizade, Shen, Wong 2022
Corollary 1.4 covers log T from about 29.95, and line 2 of 3.63, Trudgian 2014, is SUSPECT
through the gap reported by Bennett et al. 2021 page 1456 and by Hasanalizade, Shen, Wong page
222 footnote 2. INTAKE: Bellotti and Wong, arXiv 2412.15470, coverage of this window NOT checked.
COUNT TAKEN: the ONE SIDED book count `bookCount` for chi modulo 1, half weight at the ends.
Replaces `zeta_362_363_second` on this window. -/
theorem zeta_window (χ : DirichletCharacter ℂ 1) {T : ℝ} (hlo : 25.5 ≤ Real.log T)
    (hhi : Real.log T ≤ 31) :
    |bookCount χ T - bookMain 1 T - 7 / 8| ≤ 6.3 + 5 / (48 * Real.pi * T) + 0.068 / T ^ 3 := by
  sorry

/-! ### The pair count. Proved, no input. -/

/-- The book count of chi plus that of its inverse is the two sided count with half weight at
height plus or minus T. -/
theorem pair_weight_sum (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 0 < T) :
    bookCount χ T + bookCount χ⁻¹ T =
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset,
        (if |ρ.im| = T then (1 / 2 : ℝ) else 1) * (mult χ ρ : ℝ) := by
  rw [bookCount_inv]
  unfold bookCount
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  rcases lt_trichotomy ρ.im 0 with h | h | h
  · have hab : |ρ.im| = -ρ.im := abs_of_neg h
    have h3 : ¬ 0 ≤ ρ.im := not_le.mpr h
    have hn : -ρ.im ≠ 0 := by linarith
    rw [if_neg h3, if_pos h.le, zero_add, hab, halfWeight]
    by_cases hT' : -ρ.im = T
    · rw [if_pos (Or.inr hT'), if_pos hT']
    · rw [if_neg (not_or.mpr ⟨hn, hT'⟩), if_neg hT']
  · have hab : |ρ.im| ≠ T := by rw [h, abs_zero]; exact hT.ne
    rw [if_pos (le_of_eq h), if_pos (ge_of_eq h), if_neg hab, h, neg_zero]
    simp only [halfWeight, true_or, if_true]
    ring
  · have hab : |ρ.im| = ρ.im := abs_of_pos h
    have h3 : ¬ ρ.im ≤ 0 := not_le.mpr h
    rw [if_pos h.le, if_neg h3, add_zero, hab, halfWeight]
    by_cases hT' : ρ.im = T
    · rw [if_pos (Or.inr hT'), if_pos hT']
    · rw [if_neg (not_or.mpr ⟨h.ne', hT'⟩), if_neg hT']

/-- Just below height T the strip zeros are those up to T with abs Im below T. -/
theorem left_gap (χ : DirichletCharacter ℂ q) (T : ℝ) :
    ∃ ε > 0, ∀ t, T - ε < t → t < T →
      (stripZeros_finite χ t).toFinset =
        (stripZeros_finite χ T).toFinset.filter (fun ρ => |ρ.im| < T) := by
  classical
  let A : Set ℝ := (fun ρ : ℂ ↦ |ρ.im|) '' (stripZeros χ T ∩ {ρ | |ρ.im| < T})
  have hA : A.Finite := ((stripZeros_finite χ T).inter_of_left _).image _
  have hT : T ∉ A := by
    rintro ⟨ρ, ⟨_, h⟩, he⟩
    have h' : |ρ.im| < T := h
    have he' : |ρ.im| = T := he
    linarith
  have hn : Aᶜ ∈ 𝓝 T := hA.isClosed.isOpen_compl.mem_nhds hT
  obtain ⟨r, hrr, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hrr, ?_⟩
  intro t ht1 ht2
  ext ρ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · intro hρ
    exact ⟨⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans ht2.le⟩, lt_of_le_of_lt hρ.2.2.2 ht2⟩
  · rintro ⟨hρ, hlt⟩
    refine ⟨hρ.1, hρ.2.1, hρ.2.2.1, ?_⟩
    by_contra hc
    have hc' : t < |ρ.im| := not_le.mp hc
    have hmem : |ρ.im| ∈ A := ⟨ρ, ⟨hρ, hlt⟩, rfl⟩
    have hball : |ρ.im| ∈ Metric.ball T r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact hb hball hmem

lemma two_bookMain (q : ℕ) (t : ℝ) :
    2 * bookMain q t = t / Real.pi * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1)) := by
  unfold bookMain
  ring

lemma continuousAt_main2 (hq0 : (q : ℝ) ≠ 0) {T : ℝ} (hT : 0 < T) :
    ContinuousAt (fun t ↦ t / Real.pi * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))) T := by
  have hne : (q : ℝ) * T / (2 * Real.pi * Real.exp 1) ≠ 0 :=
    div_ne_zero (mul_ne_zero hq0 hT.ne') (by positivity)
  exact ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne)

lemma continuousAt_logqT (hq0 : (q : ℝ) ≠ 0) {T : ℝ} (hT : 0 < T) :
    ContinuousAt (fun t ↦ Real.log ((q : ℝ) * t)) T :=
  ContinuousAt.log (by fun_prop) (mul_ne_zero hq0 hT.ne')

/-- The pair count from `bmor_two_sided`, PROVED from that LEAF alone. The upper side is the
leaf at T, the lower side the leaf just below T and the left limit. -/
theorem pair_bmor (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 1 < q) {T : ℝ}
    (hT : 1 ≤ T) :
    |bookCount χ T + bookCount χ⁻¹ T - 2 * bookMain q T| ≤
      0.298 * Real.log ((q : ℝ) * T) + 4.358 := by
  have hT0 : 0 < T := by linarith
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [pair_weight_sum χ hT0, two_bookMain]
  set F := (stripZeros_finite χ T).toFinset with hF
  set S := ∑ ρ ∈ F, (if |ρ.im| = T then (1 / 2 : ℝ) else 1) * (mult χ ρ : ℝ) with hS
  set N := ∑ ρ ∈ F, (mult χ ρ : ℝ) with hN
  set M := ∑ ρ ∈ F.filter (fun ρ => |ρ.im| < T), (mult χ ρ : ℝ) with hM
  have hSN : S ≤ N := by
    apply Finset.sum_le_sum
    intro ρ _
    have hm : (0 : ℝ) ≤ mult χ ρ := Nat.cast_nonneg _
    split_ifs <;> linarith
  have hMS : M ≤ S := by
    rw [hM, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro ρ _
    have hm : (0 : ℝ) ≤ mult χ ρ := Nat.cast_nonneg _
    split_ifs with h1 h2
    · linarith
    · linarith
    · linarith
    · linarith
  have hup := (abs_le.mp (bmor_two_sided χ hχ hq (by linarith : (5 / 7 : ℝ) ≤ T))).2
  obtain ⟨ε, hε, hgap⟩ := left_gap χ T
  set g : ℝ → ℝ := fun t ↦ t / Real.pi * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1)) -
    (0.298 * Real.log ((q : ℝ) * t) + 4.358) with hg
  have hev : ∀ᶠ t in 𝓝[<] T, g t ≤ M := by
    have hlt : max (T - ε) (5 / 7) < T := max_lt (by linarith) (by linarith)
    filter_upwards [Ioo_mem_nhdsLT hlt] with t ht
    have h57 : (5 / 7 : ℝ) ≤ t := (lt_of_le_of_lt (le_max_right _ _) ht.1).le
    have hTe : T - ε < t := lt_of_le_of_lt (le_max_left _ _) ht.1
    have he := hgap t hTe ht.2
    have hb := (abs_le.mp (bmor_two_sided χ hχ hq h57)).1
    rw [he] at hb
    simp only [hg]
    linarith
  have hcont : ContinuousAt g T :=
    (continuousAt_main2 hq0 hT0).sub
      ((continuousAt_const.mul (continuousAt_logqT hq0 hT0)).add continuousAt_const)
  have hlim : Tendsto g (𝓝[<] T) (𝓝 (g T)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlow : g T ≤ M := le_of_tendsto hlim hev
  simp only [hg] at hlow
  rw [abs_le]
  constructor <;> linarith

/-- The REAL character case of display 3.95, PROVED from `bmor_two_sided` alone: for chi real,
chi inverse = chi, the pair count is twice the book count, and half of 0.298 log qT + 4.358 is
inside 0.15 log qT + 3.389. Count: the ONE SIDED book count. -/
theorem real_case (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hr : χ⁻¹ = χ)
    (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  have hq : 1 < q := by
    have h0 := NeZero.pos q
    by_contra h
    obtain rfl : q = 1 := by omega
    exact hne (DirichletCharacter.level_one χ)
  have h := pair_bmor χ hχ hq hT
  rw [hr] at h
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hL : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  unfold bookError
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-! ### The trivial character. Proved from the zeta LEAFs. -/

/-- log 31 is at most 3.5. -/
theorem log_31_le : Real.log 31 ≤ 3.5 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have hsplit : Real.exp 3.5 = Real.exp 1 ^ 3 * Real.exp 0.5 := by
    rw [show (3.5 : ℝ) = ((3 : ℕ) : ℝ) * 1 + 0.5 by norm_num, Real.exp_add, Real.exp_nat_mul]
  rw [hsplit]
  have he := Real.exp_one_gt_d9
  have he3 : (2.718 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hq := Real.quadratic_le_exp_of_nonneg (x := (0.5 : ℝ)) (by norm_num)
  have h3 : (0 : ℝ) ≤ Real.exp 1 ^ 3 := by positivity
  nlinarith

/-- The trivial character case of display 3.95, PROVED from `zeta_first_zero`,
`zeta_362_363_first`, `zeta_window` and `zeta_362_hsw`, with cuts at log T = 25.5 and 31.
It never uses `zeta_362_363_second`. -/
theorem zeta_case_honest (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 1 ≤ T) :
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
    · rcases le_or_gt (Real.log T) 31 with hw | hh
      · obtain ⟨a1, a2⟩ := abs_le.mp (zeta_window χ hl.le hw)
        rw [abs_le]
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := abs_le.mp (zeta_362_hsw χ hT14)
        have hLpos : 0 < Real.log T := by linarith
        have hdiv := Real.log_le_sub_one_of_pos (x := Real.log T / 31) (by positivity)
        rw [Real.log_div hLpos.ne' (by norm_num)] at hdiv
        have h31 := log_31_le
        have h' : Real.log T / 31 = Real.log T * (1 / 31) := by
          rw [div_eq_mul_inv]; norm_num
        rw [h'] at hdiv
        have hlogL : Real.log (Real.log T) ≤ 2.5 + Real.log T * (1 / 31) := by linarith
        have hlogL0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg (by linarith)
        rw [abs_le]
        constructor <;> linarith

/-! ### Assembly and twins -/

/-- ASSEMBLY. Exactly the sealed statement `ZeroCount1623.book_zero_count`, PROVED from the
LEAFs of this file and the two kept zeta LEAFs of `BookZeroSplit1122`. Case split: chi trivial
forces q = 1 and is `zeta_case_honest`; chi real non-trivial is `real_case` from
`bmor_two_sided`; chi complex is `book_395_complex`. CONDITIONAL ON those LEAFs. -/
theorem book_zero_count_honest (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  by_cases h1 : χ = 1
  · have hq : q = 1 := by
      have h := (DirichletCharacter.isPrimitive_def χ).mp hχ
      rw [h1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hq
    exact zeta_case_honest χ hT
  · by_cases hr : χ⁻¹ = χ
    · exact real_case χ hχ hr h1 hT
    · exact book_395_complex χ hχ hr hT

example : type_of% @book_zero_count_honest = type_of% @ZeroCount1623.book_zero_count := rfl

/-- The named hypothesis `MainHyps123.BookZeroCount` of the conditional main theorem, PROVED
from the honest LEAFs. CONDITIONAL ON `bmor_two_sided`, `book_395_complex`,
`BookZeroSplit1122.zeta_first_zero`, `BookZeroSplit1122.zeta_362_363_first`, `zeta_window` and
`zeta_362_hsw`; it does not use `book_395_nontrivial` or `zeta_362_363_second`. -/
theorem book_zero_count_honest_named : MainHyps123.BookZeroCount :=
  fun _ _ χ hχ _ hT => book_zero_count_honest χ hχ hT

/-- The two sided closed count from the one sided book bound for chi and its inverse, by the
right limit at T. Same argument as `ZeroCount1623.zero_count_two_sided`, with the book bound
as a hypothesis. Proved, no input. -/
theorem two_sided_of_one_sided (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 1 ≤ T)
    (hb : ∀ t : ℝ, 1 ≤ t → |bookCount χ t - bookMain q t| ≤ bookError q t ∧
      |bookCount χ⁻¹ t - bookMain q t| ≤ bookError q t) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) - 2 * bookMain q T| ≤
      2 * bookError q T := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  obtain ⟨ε, hε, hgap⟩ := exists_gap χ T
  set N := ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) with hN
  have hev : ∀ᶠ t in 𝓝[>] T, |N - 2 * bookMain q t| ≤ 2 * bookError q t := by
    have hmem : Ioo T (T + ε) ∈ 𝓝[>] T := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [hmem] with t ht
    have ht1 : 1 ≤ t := hT.trans ht.1.le
    have he := hgap t ht.1 ht.2
    have hnot : ∀ ρ ∈ stripZeros χ t, |ρ.im| ≠ t := by
      intro ρ hρ h
      rw [he] at hρ
      have := hρ.2.2.2
      linarith [ht.1]
    have hs := two_sided_split χ (by linarith) hnot
    have hNt : N = bookCount χ t + bookCount χ⁻¹ t := by
      rw [hN, ← sum_eq_of_strip_eq χ he, hs]
    have h1 := abs_le.mp (hb t ht1).1
    have h2 := abs_le.mp (hb t ht1).2
    rw [hNt, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hcont1 : ContinuousAt (fun t ↦ bookMain q t) T := by
    unfold bookMain
    have hne : (q : ℝ) * T / (2 * Real.pi * Real.exp 1) ≠ 0 :=
      div_ne_zero (mul_ne_zero hq0 (by linarith)) (by positivity)
    exact ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne)
  have hcont2 : ContinuousAt (fun t ↦ bookError q t) T := by
    unfold bookError
    have hne : (q : ℝ) * T ≠ 0 := mul_ne_zero hq0 (by linarith)
    exact ContinuousAt.add (ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne))
      (by fun_prop)
  have hL : Tendsto (fun t ↦ |N - 2 * bookMain q t|) (𝓝[>] T) (𝓝 |N - 2 * bookMain q T|) :=
    ((continuousAt_const.sub (continuousAt_const.mul hcont1)).abs).tendsto.mono_left
      nhdsWithin_le_nhds
  have hR : Tendsto (fun t ↦ 2 * bookError q t) (𝓝[>] T) (𝓝 (2 * bookError q T)) :=
    (continuousAt_const.mul hcont2).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hL hR hev

/-- The two sided count for q above 1 straight from `bmor_two_sided`, bypassing the footnote 5
halving. CONDITIONAL ON `bmor_two_sided` alone. -/
theorem zero_count_two_sided_bmor (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 1 < q)
    {T : ℝ} (hT : 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) - 2 * bookMain q T| ≤
      2 * bookError q T := by
  have h := bmor_two_sided χ hχ hq (by linarith : (5 / 7 : ℝ) ≤ T)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hL : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  rw [two_bookMain]
  refine h.trans ?_
  unfold bookError
  linarith

/-- Twin of `ZeroCount1623.zero_count_two_sided`, same statement. For q above 1 CONDITIONAL ON
`bmor_two_sided` alone; for q = 1 CONDITIONAL ON the zeta LEAFs through `zeta_case_honest`.
It never uses `book_395_complex`. -/
theorem zero_count_two_sided_honest (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) - 2 * bookMain q T| ≤
      2 * bookError q T := by
  rcases Nat.lt_or_ge 1 q with hq | hq
  · exact zero_count_two_sided_bmor χ hχ hq hT
  · have h0 := NeZero.pos q
    obtain rfl : q = 1 := by omega
    exact two_sided_of_one_sided χ hT fun t ht => ⟨zeta_case_honest χ ht, zeta_case_honest χ⁻¹ ht⟩

example : type_of% @zero_count_two_sided_honest = type_of% @ZeroCount1623.zero_count_two_sided :=
  rfl

/-- Twin of `ZeroCount1623.arxiv_zero_count`, same statement, arXiv 1305.2897v4 pages 37 and 38,
displays 4.25 and 4.26. Same conditions as `zero_count_two_sided_honest`. -/
theorem arxiv_zero_count_honest (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) -
      T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1))| ≤
        0.5 * Real.log ((q : ℝ) * T) + 17.7 := by
  have h := zero_count_two_sided_honest χ hχ hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  rw [two_bookMain] at h
  refine h.trans ?_
  unfold bookError
  linarith

example : type_of% @arxiv_zero_count_honest = type_of% @ZeroCount1623.arxiv_zero_count := rfl

/-- Page 39 of the arXiv version, the N of 1 paragraph. Twin of the ZeroCount1623 statement, its proof with `arxiv_zero_count_honest`.
CONDITIONAL ON `bmor_two_sided` for q above 1 and on the zeta LEAFs for q = 1.
The indicator cuts the sum at height 1, so the height T of the index plays no part. -/
theorem very_low_count_honest (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : ZeroIdx χ T, Set.indicator {ρ : ZeroIdx χ T | |ρ.val.im| ≤ 1}
        (fun ρ => (mult χ ρ.val : ℝ)) ρ) ≤ 0.819 * Real.log q + 16.8 := by
  have hpt : ∀ ρ : ZeroIdx χ T, Set.indicator {ρ : ZeroIdx χ T | |ρ.val.im| ≤ 1}
      (fun ρ => (mult χ ρ.val : ℝ)) ρ = lowTerm χ ρ.val := by
    intro ρ
    by_cases h : |ρ.val.im| ≤ 1 <;> simp [Set.indicator, lowTerm, h]
  have hsub : (stripZeros_finite χ 1).toFinset ⊆ (stripZeros_finite χ T).toFinset := by
    intro ρ hρ
    have hρ' := (stripZeros_finite χ 1).mem_toFinset.mp hρ
    exact (stripZeros_finite χ T).mem_toFinset.mpr
      ⟨hρ'.1, hρ'.2.1, hρ'.2.2.1, hρ'.2.2.2.trans hT⟩
  have hzero : ∀ ρ ∈ (stripZeros_finite χ T).toFinset,
      ρ ∉ (stripZeros_finite χ 1).toFinset → lowTerm χ ρ = 0 := by
    intro ρ hT' hn
    have hρ' := (stripZeros_finite χ T).mem_toFinset.mp hT'
    have hh : ¬ |ρ.im| ≤ 1 := fun h => hn
      ((stripZeros_finite χ 1).mem_toFinset.mpr ⟨hρ'.1, hρ'.2.1, hρ'.2.2.1, h⟩)
    simp [lowTerm, hh]
  have hsame : (∑ ρ ∈ (stripZeros_finite χ 1).toFinset, lowTerm χ ρ) =
      ∑ ρ ∈ (stripZeros_finite χ 1).toFinset, (mult χ ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    unfold lowTerm
    rw [ite_eq_left ((stripZeros_finite χ 1).mem_toFinset.mp hρ).2.2.2]
  have hreduce : (∑' ρ : ZeroIdx χ T, Set.indicator {ρ : ZeroIdx χ T | |ρ.val.im| ≤ 1}
      (fun ρ => (mult χ ρ.val : ℝ)) ρ) =
      ∑ ρ ∈ (stripZeros_finite χ 1).toFinset, (mult χ ρ : ℝ) :=
    (tsum_congr hpt).trans ((tsum_zeroIdx χ T (lowTerm χ)).trans
      ((Finset.sum_subset hsub hzero).symm.trans hsame))
  rw [hreduce]
  have h := (abs_le.mp (arxiv_zero_count_honest χ hχ (le_refl (1 : ℝ)))).2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (q : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < q).ne'
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  simp only [mul_one] at h
  rw [Real.log_div hq0 (by positivity)] at h
  have hl := log_two_pi_e_ge
  have hpi := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hip : (1 : ℝ) / Real.pi ≤ 0.319 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith
  have hip2 : (0.3183 : ℝ) ≤ 1 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]; nlinarith
  have hA : 1 / Real.pi * Real.log q ≤ 0.319 * Real.log q :=
    mul_le_mul_of_nonneg_right hip hlq
  have hB : 0.3183 * (2.8294 : ℝ) ≤ 1 / Real.pi * Real.log (2 * Real.pi * Real.exp 1) :=
    mul_le_mul hip2 hl (by norm_num) (by positivity)
  have hexp : 1 / Real.pi * (Real.log q - Real.log (2 * Real.pi * Real.exp 1)) =
      1 / Real.pi * Real.log q - 1 / Real.pi * Real.log (2 * Real.pi * Real.exp 1) := by ring
  rw [hexp] at h
  have hnum : (0.9 : ℝ) ≤ 0.3183 * 2.8294 := by norm_num
  linarith

/-- Page 38 of the arXiv version, the upper side of display 4.26 as a sum over the index type.
Twin of the ZeroCount1623 statement, its proof with `arxiv_zero_count_honest`.
CONDITIONAL ON `bmor_two_sided` for q above 1 and on the zeta LEAFs for q = 1. -/
theorem strip_count_honest (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : ZeroIdx χ T, (mult χ ρ.val : ℝ)) ≤
      T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) +
        0.5 * Real.log ((q : ℝ) * T) + 17.7 := by
  have e : (∑' ρ : ZeroIdx χ T, (mult χ ρ.val : ℝ)) =
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) :=
    tsum_zeroIdx χ T (fun z => (mult χ z : ℝ))
  rw [e]
  have h := (abs_le.mp (arxiv_zero_count_honest χ hχ hT)).2
  linarith

example : type_of% @very_low_count_honest = type_of% @ZeroCount1623.very_low_count := rfl

example : type_of% @strip_count_honest = type_of% @ZeroCount1623.strip_count := rfl

end LeanLab.HelfgottMajor.BookZeroHonest1123
