/-
Split of helfgott_theorem63_minor_inputs from Feed1122Decomp420b.
Helfgott https://arxiv.org/abs/1312.7748v2, proof of Theorem 6.3 on pages 50 to 52
and its application in section 7.3, pages 62, 63 and 69, equations 7.26, 7.27,
7.30, 7.47 and 7.48. The prime sum over primes above the square root of x is
split from the rest as on page 50; the weighted triangle inequality, the bound
for the small or non-prime part and the bound for the large prime part are
separate leaves. The book 1501.05438 page 274 correction turns 0.77671 into 0.77962.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp420b

namespace LeanLab.Ternary.Task420
open Finset MeasureTheory
open LeanLab.Ternary.MMS

/-! Helper lemmas for the page 50 leaves: a weighted L2 triangle inequality, Parseval
for absolutely summable real coefficients, and continuity of the exponential sums.
Helfgott 1312.7748v2 page 50. -/

/-- A real optimisation step: a bound by 1 plus t times A plus 1 plus 1 over t times B for
every positive t gives the square of root A plus root B.
Helfgott 1312.7748v2 page 50, the weighted triangle inequality. -/
theorem sq_add_sqrt_of_forall {L A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → L ≤ (1 + t) * A + (1 + 1 / t) * B) :
    L ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
  set s := Real.sqrt A with hs
  set r := Real.sqrt B with hr
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hA' : A = s ^ 2 := (Real.sq_sqrt hA).symm
  have hB' : B = r ^ 2 := (Real.sq_sqrt hB).symm
  apply le_of_forall_pos_le_add
  intro δ hδ
  set ε := δ / (s + r + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hεδ : ε * (s + r) ≤ δ := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have ht := h ((r + ε) / (s + ε)) (by positivity)
  have hse : 0 < s + ε := by positivity
  have hre : 0 < r + ε := by positivity
  have e1 : (1 + (r + ε) / (s + ε)) * A + (1 + 1 / ((r + ε) / (s + ε))) * B =
      A + B + (r + ε) * (s ^ 2 / (s + ε)) + (s + ε) * (r ^ 2 / (r + ε)) := by
    rw [hA', hB']; field_simp; ring
  have h1 : s ^ 2 / (s + ε) ≤ s := by
    rw [div_le_iff₀ hse]; nlinarith
  have h2 : r ^ 2 / (r + ε) ≤ r := by
    rw [div_le_iff₀ hre]; nlinarith
  have h3 : (r + ε) * (s ^ 2 / (s + ε)) ≤ (r + ε) * s := mul_le_mul_of_nonneg_left h1 hre.le
  have h4 : (s + ε) * (r ^ 2 / (r + ε)) ≤ (s + ε) * r := mul_le_mul_of_nonneg_left h2 hse.le
  rw [e1] at ht
  nlinarith

/-- Weighted L2 triangle inequality on a subset of the unit interval. -/
theorem weighted_triangle_integral {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Icc 0 1) {W F G : ℝ → ℂ}
    (hW : Continuous W) (hF : Continuous F) (hG : Continuous G) :
    (∫ α in s, ‖F α‖ ^ 2 * ‖W α‖) ≤
      (Real.sqrt (∫ α in s, ‖W α‖ * ‖G α‖ ^ 2) +
        Real.sqrt (∫ α in s, ‖W α‖ * ‖F α - G α‖ ^ 2)) ^ 2 := by
  have hint : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f s := fun f hf =>
    hf.integrableOn_Icc.mono_set hsub
  apply sq_add_sqrt_of_forall
    (setIntegral_nonneg hs (fun α _ => by positivity))
    (setIntegral_nonneg hs (fun α _ => by positivity))
  intro t ht
  have iA : IntegrableOn (fun α => ‖W α‖ * ‖G α‖ ^ 2) s :=
    hint _ (hW.norm.mul (hG.norm.pow 2))
  have iB : IntegrableOn (fun α => ‖W α‖ * ‖F α - G α‖ ^ 2) s :=
    hint _ (hW.norm.mul ((hF.sub hG).norm.pow 2))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iA.const_mul _) (iB.const_mul _)]
  apply setIntegral_mono_on (hint (fun α => ‖F α‖ ^ 2 * ‖W α‖) ((hF.norm.pow 2).mul hW.norm))
    ((iA.const_mul _).add (iB.const_mul _)) hs
  intro α _
  have htri : ‖F α‖ ≤ ‖G α‖ + ‖F α - G α‖ := by
    calc ‖F α‖ = ‖G α + (F α - G α)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  set a := ‖G α‖
  set b := ‖F α - G α‖
  set w := ‖W α‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hw : 0 ≤ w := norm_nonneg _
  have hf0 : 0 ≤ ‖F α‖ := norm_nonneg _
  have hsq : ‖F α‖ ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hf0 htri 2
  have hkey : (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2 := by
    have : (1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2 - (a + b) ^ 2 = (t * a - b) ^ 2 / t := by
      field_simp; ring
    have : 0 ≤ (t * a - b) ^ 2 / t := by positivity
    linarith
  calc ‖F α‖ ^ 2 * w ≤ ((1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2) * w :=
        mul_le_mul_of_nonneg_right (hsq.trans hkey) hw
    _ = (1 + t) * (w * a ^ 2) + (1 + 1 / t) * (w * b ^ 2) := by ring

/-- The conjugate of e of t is e of minus t.
Helfgott 1312.7748v2 page 10 notation, used for Parseval on page 50. -/
theorem conj_e_real (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Parseval for absolutely summable real coefficients. -/
theorem parseval_charSeries_real (r : ℕ → ℝ) (hr : Summable fun n => |r n|) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖charSeries (fun n => (r n : ℂ)) α‖ ^ 2) =
      ∑' n, r n ^ 2 := by
  have hrn : Summable fun n => ‖(r n : ℂ)‖ := by
    simp only [Complex.norm_real, Real.norm_eq_abs]; exact hr
  have hprod : Summable fun i : ℕ × ℕ => ‖(r i.1 : ℂ) * (r i.2 : ℂ)‖ := by
    simpa only [norm_mul] using hrn.mul_norm hrn
  have hexp (α : ℝ) : charSeries (fun n => (r n : ℂ)) α *
      (starRingEnd ℂ) (charSeries (fun n => (r n : ℂ)) α) =
      ∑' i : ℕ × ℕ, ((r i.1 : ℂ) * (r i.2 : ℂ)) * e ((((i.1 : ℤ) - i.2 : ℤ) : ℝ) * α) := by
    have h1 : Summable fun n => ‖(r n : ℂ) * e ((n : ℝ) * α)‖ := by
      simpa only [norm_mul, norm_e, mul_one] using hrn
    have h2 : Summable fun n => ‖(r n : ℂ) * e (-((n : ℝ) * α))‖ := by
      simpa only [norm_mul, norm_e, mul_one] using hrn
    unfold charSeries
    rw [Complex.conj_tsum]
    have hc : ∀ n : ℕ, (starRingEnd ℂ) ((r n : ℂ) * e ((n : ℝ) * α)) =
        (r n : ℂ) * e (-((n : ℝ) * α)) := by
      intro n
      rw [map_mul, Complex.conj_ofReal, conj_e_real]
    simp_rw [hc]
    rw [tsum_mul_tsum_of_summable_norm h1 h2]
    apply tsum_congr
    intro i
    have : e ((i.1 : ℝ) * α) * e (-((i.2 : ℝ) * α)) = e ((((i.1 : ℤ) - i.2 : ℤ) : ℝ) * α) := by
      rw [← e_add]; congr 1; push_cast; ring
    rw [← this]; ring
  have hnorm (α : ℝ) : ((‖charSeries (fun n => (r n : ℂ)) α‖ ^ 2 : ℝ) : ℂ) =
      charSeries (fun n => (r n : ℂ)) α *
        (starRingEnd ℂ) (charSeries (fun n => (r n : ℂ)) α) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hnorm, hexp]
  rw [integral_l1_characters _ _ hprod, Complex.ofReal_tsum]
  have hsupp : Function.support (fun i : ℕ × ℕ =>
      if (((i.1 : ℤ) - i.2 : ℤ)) = 0 then (r i.1 : ℂ) * (r i.2 : ℂ) else 0) ⊆
      Set.range (fun n : ℕ => (n, n)) := by
    intro i hi
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hi
    obtain ⟨h, _⟩ := hi
    exact ⟨i.1, Prod.ext rfl (by simp; omega)⟩
  rw [← (show Function.Injective (fun n : ℕ => (n, n)) from
    fun a b h => by simpa using congrArg Prod.fst h).tsum_eq hsupp]
  apply tsum_congr
  intro n
  simp [sq]


/-- A restricted part of the exponential sum is the character series of the restricted coefficients. -/
theorem S_part_eq_charSeries (P : ℕ → Prop) [DecidablePred P] (η : ℝ → ℝ) (x α : ℝ) :
    (∑' n : ℕ, if P n then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        LeanLab.HelfgottArcs.e (α * n) * (η (n / x) : ℂ) else 0) =
      charSeries (fun n => if P n then ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (η (n / x) : ℂ) else 0) α := by
  unfold charSeries
  apply tsum_congr
  intro n
  have he : LeanLab.HelfgottArcs.e (α * n) = e ((n : ℝ) * α) := by
    unfold LeanLab.HelfgottArcs.e e
    congr 1
    push_cast
    ring
  by_cases h : P n
  · simp only [h, ite_true, he]; ring
  · simp only [h, ite_false, zero_mul]

/-- A restriction of an absolutely summable sequence by a predicate is absolutely summable.
Helfgott 1312.7748v2 page 50, the split of S eta plus. -/
theorem summable_part_of_summable (P : ℕ → Prop) [DecidablePred P] (c : ℕ → ℂ)
    (hc : Summable fun n => ‖c n‖) : Summable fun n => ‖if P n then c n else 0‖ := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hc
  intro n
  split_ifs <;> simp

/-- The length x is positive for N at least 10 to the 27.
Helfgott 1312.7748v2 page 59. -/
theorem xOf_pos (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) : 0 < LeanLab.Helfgott2013.xOf N := by
  unfold LeanLab.Helfgott2013.xOf LeanLab.Helfgott2013.ratio
  have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  positivity

/-- The minor arcs lie in the closed unit interval.
Helfgott 1312.7748v2 page 10, equation 3.5. -/
theorem minor_sub_Icc (x : ℝ) : Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs x ⊆ Set.Icc 0 1 :=
  Set.sdiff_subset.trans Set.Ioc_subset_Icc_self

/-- The minor arcs form a measurable set.
Helfgott 1312.7748v2 page 10, equation 3.5. -/
theorem measurableSet_minor (x : ℝ) : MeasurableSet (Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs x) :=
  measurableSet_Ioc.diff (measurableSet_helfgottMajorArcs x)

/-- S eta plus is continuous in alpha.
Helfgott 1312.7748v2 page 50. -/
theorem continuous_S_etaPlus {x : ℝ} (hx : 0 < x) :
    Continuous fun α => LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α x := by
  simp_rw [S_eq_charSeries]
  exact continuous_charSeries _ (etaPlus_coefficients_summable hx)

/-- S eta star is continuous in alpha.
Helfgott 1312.7748v2 page 50. -/
theorem continuous_S_etaStar {x : ℝ} (hx : 0 < x) :
    Continuous fun α => LeanLab.HelfgottArcs.S
      (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
        LeanLab.HelfgottArcs.etaT2 (49 * t)) α x := by
  simp_rw [S_eq_charSeries]
  exact continuous_charSeries _ (etaStar_coefficients_summable hx)

/-- Any restricted part of S eta plus is continuous in alpha.
Helfgott 1312.7748v2 page 50, the sum S one. -/
theorem continuous_S_part (P : ℕ → Prop) [DecidablePred P] {x : ℝ} (hx : 0 < x) :
    Continuous fun α => ∑' n : ℕ, (if P n then
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ) else 0) := by
  simp_rw [S_part_eq_charSeries]
  exact continuous_charSeries _ (summable_part_of_summable P _ (etaPlus_coefficients_summable hx))

/-- Eta star at a nonnegative argument is nonnegative.
Helfgott 1312.7748v2 page 60, equation 7.19. -/
theorem etaStar_nonneg_scaled (x : ℝ) (hx : 0 < x) (n : ℕ) :
    0 ≤ LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
      (49 * (n / x)) := by
  rw [etaStar_eq_mellin (by positivity)]
  exact (LeanLab.Helfgott2013.MellinSup.mellin_sup _).1

/-- The absolute value of S eta star is at most S eta star at zero.
Helfgott 1312.7748v2 page 50, the display after Clearly. -/
theorem norm_S_etaStar_le {x : ℝ} (hx : 0 < x) (α : ℝ) :
    ‖LeanLab.HelfgottArcs.S
      (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
        LeanLab.HelfgottArcs.etaT2 (49 * t)) α x‖ ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
          (49 * (n / x)) := by
  have hs := etaStar_coefficients_summable hx
  have hn (n : ℕ) : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      LeanLab.HelfgottArcs.e (α * n) *
      ((LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
        (49 * (n / x)) : ℝ) : ℂ)‖ = (ArithmeticFunction.vonMangoldt n : ℝ) *
        LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
          (49 * (n / x)) := by
    have he : ‖LeanLab.HelfgottArcs.e (α * n)‖ = 1 := LeanLab.Ternary.MMS.norm_e _
    rw [norm_mul, norm_mul, he, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_nonneg (etaStar_nonneg_scaled x hx n)]
  have hs' : Summable fun n : ℕ => ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      LeanLab.HelfgottArcs.e (α * n) *
      ((LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
        (49 * (n / x)) : ℝ) : ℂ)‖ := by
    simp_rw [hn]
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_nonneg (etaStar_nonneg_scaled x hx _)] using hs
  unfold LeanLab.HelfgottArcs.S
  refine (norm_tsum_le_tsum_norm hs').trans (le_of_eq ?_)
  exact tsum_congr hn

/-- S two, the difference of S eta plus and S one, is the character series of the non prime or small coefficients.
Helfgott 1312.7748v2 page 50. -/
theorem S_etaPlus_sub_part {x : ℝ} (hx : 0 < x) (α : ℝ) :
    LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α x -
      ∑' n : ℕ, (if n.Prime ∧ Real.sqrt x < n then
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
          (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ) else 0) =
      charSeries (fun n => ((if n.Prime ∧ Real.sqrt x < n then 0 else
        (ArithmeticFunction.vonMangoldt n : ℝ) * LeanLab.HelfgottArcs.etaPlus (n / x) : ℝ) : ℂ))
        α := by
  rw [S_eq_charSeries, S_part_eq_charSeries]
  have h1 := etaPlus_coefficients_summable hx
  have h2 := summable_part_of_summable (fun n : ℕ => n.Prime ∧ Real.sqrt x < n) _ h1
  unfold charSeries
  have hs1 : Summable fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ) * e ((n : ℝ) * α) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_e, mul_one] using h1
  have hs2 : Summable fun n : ℕ => (if n.Prime ∧ Real.sqrt x < n then
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ) else 0) * e ((n : ℝ) * α) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_e, mul_one] using h2
  rw [← hs1.tsum_sub hs2]
  apply tsum_congr
  intro n
  by_cases h : n.Prime ∧ Real.sqrt x < n
  · simp only [h, and_self, ite_true]; push_cast; ring
  · simp only [h, ite_false]; push_cast; ring


/-- Proved, formerly a LEAF. Helfgott 1312.7748v2 page 50, the triangle inequality with weights
the absolute value of S eta star, after writing S eta plus as S one plus S two,
where S one is the sum over primes p above the square root of x, MEDIUM.
The minor arc integral of the Fourier norm is at most the square of the sum of the
square roots of the two weighted integrals of the squares of S one and S two. -/
theorem helfgott_minor_weighted_triangle (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖helfgottIntegrand N α‖) ≤
      (Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
          ‖LeanLab.HelfgottArcs.S
            (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
              LeanLab.HelfgottArcs.etaT2 (49 * t)) α (LeanLab.Helfgott2013.xOf N)‖ *
          ‖∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
                (LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) : ℂ)
            else 0)‖ ^ 2) +
        Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
          ‖LeanLab.HelfgottArcs.S
            (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
              LeanLab.HelfgottArcs.etaT2 (49 * t)) α (LeanLab.Helfgott2013.xOf N)‖ *
          ‖LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α (LeanLab.Helfgott2013.xOf N) -
            ∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
                (LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) : ℂ)
            else 0)‖ ^ 2)) ^ 2 := by
  have hx := xOf_pos N hN
  simp_rw [norm_helfgottIntegrand]
  exact weighted_triangle_integral (measurableSet_minor _) (minor_sub_Icc _)
    (continuous_S_etaStar hx) (continuous_S_etaPlus hx) (continuous_S_part _ hx)

/-- Proved, formerly a LEAF. Helfgott 1312.7748v2 page 50, the display after Clearly: the weighted
integral of the square of S two is at most the maximum of S eta star, which is
the sum of Lambda of n times eta star of n over x, times the integral of the square
of S two over the circle, which by Parseval is the sum of Lambda of n squared
times eta plus of n over x squared over n non-prime or n at most root x, MEDIUM. -/
theorem helfgott_minor_small_part_parseval (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖LeanLab.HelfgottArcs.S
          (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
            LeanLab.HelfgottArcs.etaT2 (49 * t)) α (LeanLab.Helfgott2013.xOf N)‖ *
        ‖LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α (LeanLab.Helfgott2013.xOf N) -
          ∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
              (LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) : ℂ)
          else 0)‖ ^ 2) ≤
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
            (49 * (n / LeanLab.Helfgott2013.xOf N))) *
        ∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then 0 else
          (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
            LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2) := by
  have hx := xOf_pos N hN
  set x := LeanLab.Helfgott2013.xOf N
  set W0 := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
        (49 * (n / x))
  set r : ℕ → ℝ := fun n => if n.Prime ∧ Real.sqrt x < n then 0 else
        (ArithmeticFunction.vonMangoldt n : ℝ) * LeanLab.HelfgottArcs.etaPlus (n / x) with hr
  have hD (α : ℝ) := S_etaPlus_sub_part hx α
  simp_rw [hD]
  have hrs : Summable fun n => ‖((r n : ℝ) : ℂ)‖ := by
    have h2 := summable_part_of_summable (fun n : ℕ => ¬ (n.Prime ∧ Real.sqrt x < n)) _
      (etaPlus_coefficients_summable hx)
    refine h2.congr (fun n => ?_)
    by_cases h : n.Prime ∧ Real.sqrt x < n
    · simp [r, h]
    · simp only [r, h, ite_false, not_false_eq_true, ite_true]; push_cast; rfl
  have hrs' : Summable fun n => |r n| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hrs
  have hcD : Continuous fun α => charSeries (fun n => ((r n : ℝ) : ℂ)) α :=
    continuous_charSeries _ hrs
  have hW0 : 0 ≤ W0 := tsum_nonneg (fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (etaStar_nonneg_scaled x hx n))
  have hpar := parseval_charSeries_real r hrs'
  have hsq : (∑' n, r n ^ 2) = ∑' n : ℕ, (if n.Prime ∧ Real.sqrt x < n then 0 else
          (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
            LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2) := by
    apply tsum_congr; intro n
    by_cases h : n.Prime ∧ Real.sqrt x < n
    · simp [r, h]
    · simp only [r, h, ite_false]; ring
  rw [← hsq, ← hpar, ← integral_const_mul]
  have hI : IntegrableOn (fun α => W0 * ‖charSeries (fun n => ((r n : ℝ) : ℂ)) α‖ ^ 2)
      (Set.Ioc (0 : ℝ) 1) :=
    (continuous_const.mul (hcD.norm.pow 2)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  calc _ ≤ ∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs x,
        W0 * ‖charSeries (fun n => ((r n : ℝ) : ℂ)) α‖ ^ 2 := by
        apply setIntegral_mono_on _ (hI.mono_set Set.sdiff_subset) (measurableSet_minor x)
        · intro α _
          exact mul_le_mul_of_nonneg_right (norm_S_etaStar_le hx α) (by positivity)
        · exact (((continuous_S_etaStar hx).norm.mul (hcD.norm.pow 2)).integrableOn_Icc).mono_set
            (minor_sub_Icc x)
    _ ≤ _ := by
        apply setIntegral_mono_set hI
        · exact Filter.Eventually.of_forall (fun α => by positivity)
        · exact Set.sdiff_subset.eventuallyLE

/-- LEAF: Helfgott 1312.7748v2 page 51, the bounds from RS62 Theorems 12 and 13
giving the quantity E of 6.10, followed by page 63 equation 7.26 with x at least
4.9e26: the sum of Lambda of n squared times eta plus of n over x squared over n
non-prime or n at most root x is at most 8.4031e-12 x, MEDIUM. -/
theorem helfgott_E_bound (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then 0 else
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
          LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2)) ≤
      8.4031e-12 * LeanLab.Helfgott2013.xOf N := by
  sorry

/-- LEAF: Helfgott 1312.7748v2 page 63, the display before 7.27, from 7.16 and 7.20:
S eta star at zero is at most root pi over 2 plus 1.9075e-8, times x over kappa, MEDIUM. -/
theorem helfgott_Sstar_zero_upper (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
          (49 * (n / LeanLab.Helfgott2013.xOf N))) ≤
      (Real.sqrt (Real.pi / 2) + 1.9075e-8) * LeanLab.Helfgott2013.xOf N /
        LeanLab.Helfgott2013.κ := by
  sorry

/-- LEAF: Helfgott 1312.7748v2 pages 51 and 52, Proposition 6.2 applied with
Corollary 5.7 and the minor arc bound 6.16, giving 6.19, so that the weighted
integral of the square of S one is at most the L1 norm root pi over 2 of phi times
x over kappa times M plus T, with M at most 0.77962 x by the repaired 7.47, book
1501.05438 page 274, and T at most 3.5776e-4 x by page 63 equation 7.30, HARD. -/
theorem helfgott_minor_large_prime_part (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖LeanLab.HelfgottArcs.S
          (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
            LeanLab.HelfgottArcs.etaT2 (49 * t)) α (LeanLab.Helfgott2013.xOf N)‖ *
        ‖∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
              (LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) : ℂ)
          else 0)‖ ^ 2) ≤
      Real.sqrt (Real.pi / 2) * LeanLab.Helfgott2013.xOf N *
        (0.77962 * LeanLab.Helfgott2013.xOf N + 3.5776e-4 * LeanLab.Helfgott2013.xOf N) /
          LeanLab.Helfgott2013.κ := by
  sorry

/-- The product of the two page 63 bounds is the 7.27 bound 1.0532e-11 x squared
over kappa. Helfgott 1312.7748v2 page 63 equation 7.27. -/
theorem helfgott_727_arith {x A B : ℝ} (hx : 0 ≤ x) (hB0 : 0 ≤ B)
    (hA : A ≤ (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / LeanLab.Helfgott2013.κ)
    (hB : B ≤ 8.4031e-12 * x) :
    A * B ≤ 1.0532e-11 * x ^ 2 / LeanLab.Helfgott2013.κ := by
  have hs := LeanLab.Helfgott2013.sqrt_pi_half_lt
  have hs0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hk : LeanLab.Helfgott2013.κ = 49 := rfl
  rw [hk] at hA ⊢
  have hU0 : 0 ≤ (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / 49 := by positivity
  have h1 : A * B ≤ (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / 49 * (8.4031e-12 * x) :=
    mul_le_mul hA hB hB0 hU0
  refine h1.trans ?_
  have : (Real.sqrt (Real.pi / 2) + 1.9075e-8) * 8.4031e-12 ≤ (1.0532e-11 : ℝ) := by
    nlinarith
  have hx2 : 0 ≤ x ^ 2 / 49 := by positivity
  have e1 : (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / 49 * (8.4031e-12 * x) =
      ((Real.sqrt (Real.pi / 2) + 1.9075e-8) * 8.4031e-12) * (x ^ 2 / 49) := by ring
  have e2 : 1.0532e-11 * x ^ 2 / 49 = 1.0532e-11 * (x ^ 2 / 49) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right this hx2

/-- The leaf helfgott_theorem63_minor_inputs from the page 50 to 52 steps of the
proof of Theorem 6.3 and the section 7.3 inputs 7.26, 7.27, 7.30 and repaired 7.47.
Helfgott 1312.7748v2 page 69 equation 7.48. -/
theorem helfgott_theorem63_minor_inputs_of_leaves (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    ∃ M T P : ℝ, 0 ≤ M + T ∧ 0 ≤ P ∧
      M ≤ 0.77962 * LeanLab.Helfgott2013.xOf N ∧
      T ≤ 3.5776e-4 * LeanLab.Helfgott2013.xOf N ∧
      P ≤ 1.0532e-11 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ ∧
      (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖helfgottIntegrand N α‖) ≤
        (Real.sqrt (Real.sqrt (Real.pi / 2) * LeanLab.Helfgott2013.xOf N * (M + T) /
            LeanLab.Helfgott2013.κ) + Real.sqrt P) ^ 2 := by
  have hx : 0 ≤ LeanLab.Helfgott2013.xOf N := by
    unfold LeanLab.Helfgott2013.xOf LeanLab.Helfgott2013.ratio
    positivity
  have hk0 : (0 : ℝ) < LeanLab.Helfgott2013.κ := by
    unfold LeanLab.Helfgott2013.κ; norm_num
  have hTri := helfgott_minor_weighted_triangle N hN
  have hPar := helfgott_minor_small_part_parseval N hN
  have hE := helfgott_E_bound N hN
  have hS0 := helfgott_Sstar_zero_upper N hN
  have hLarge := helfgott_minor_large_prime_part N hN
  have hE0 : 0 ≤ (∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then 0 else
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
        LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2)) := by
    apply tsum_nonneg
    intro n
    split_ifs
    · exact le_refl 0
    · positivity
  have hSmall := hPar.trans (helfgott_727_arith hx hE0 hS0 hE)
  refine ⟨0.77962 * LeanLab.Helfgott2013.xOf N, 3.5776e-4 * LeanLab.Helfgott2013.xOf N,
    1.0532e-11 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ,
    by positivity, by positivity, le_refl _, le_refl _, le_refl _, ?_⟩
  refine hTri.trans ?_
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add (Real.sqrt_le_sqrt hLarge) (Real.sqrt_le_sqrt hSmall)

end LeanLab.Ternary.Task420
