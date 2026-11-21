import LeanLab.HelfgottMajor.Gaussian123Base
import LeanLab.HelfgottMajor.MainHyps123

/-!
HELFGOTT MAIN THEOREM burst, session CLOUD-burst20261120c, unit tail, 2026-11-21.
P0014, Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, Lemma 4.5, page 41,
displays 4.33 to 4.35, the zero sum step `SplitGaussian123.tail_mass_of_corollary`.

The cited zero count of display 4.26, page 38, enters only as the named hypothesis
`MainHyps123.BookZeroCount`. The count lemmas of ZeroCount1623 that the tail step uses are
re-derived here from that hypothesis, so nothing below calls the open leaf
`ZeroCount1623.book_zero_count`.

PROVED from hB and hcor: the summability half of the sealed statement, for every shift.
SPLIT: the bound half is one LEAF, `tail_mass_bound_leaf`, and the sealed statement is
assembled from hB and that leaf with no further gap.

QUESTION on the leaf, see notes/burst-20261120c/tail.md. The numeric screen at q = 1 with
zeta zeros finds the sealed statement TRUE at T = 100, 111, 200 for every tested shift, with
ratio at most 0.1. But Helfgott's route does not prove it: display 4.35 fails at q = 1,
T = 200, δ = 0, where the one sided envelope sum is 1.99227e-13 against the integral
1.94086e-13, because page 38 drops the boundary term f(y) g(y) of display 4.27; and the
pairing of display 4.33 is wrong for complex χ. The sealed bound holds only because the true
Mellin values are far below the envelope of Corollary 3.2, which hcor does not see.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainTail123
open Real Filter Topology LeanLab.HelfgottArcs
open LeanLab.HelfgottMajor.SplitGaussian123

section Count
open ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- PROVED, CONDITIONAL ON hB, the cited count of P0014 display 4.26, page 38.
Same statement and proof as `ZeroCount1623.zero_count_two_sided`, with the open leaf
replaced by the named hypothesis. -/
theorem zero_count_two_sided_of_book (hB : MainHyps123.BookZeroCount)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ)) - 2 * bookMain q T| ≤
      2 * bookError q T := by
  have hχi : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hχ
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  obtain ⟨ε, hε, hgap⟩ := exists_gap χ T
  set N := ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) with hN
  have hev : ∀ᶠ t in 𝓝[>] T, |N - 2 * bookMain q t| ≤ 2 * bookError q t := by
    have hmem : Set.Ioo T (T + ε) ∈ 𝓝[>] T := Ioo_mem_nhdsGT (by linarith)
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
    have h1 := abs_le.mp (hB q χ hχ ht1)
    have h2 := abs_le.mp (hB q χ⁻¹ hχi ht1)
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

/-- PROVED, CONDITIONAL ON hB. P0014 page 38, the upper side of display 4.26 as a sum over
the index type. Same statement as `ZeroCount1623.strip_count`. -/
theorem strip_count_of_book (hB : MainHyps123.BookZeroCount)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    (∑' ρ : ZeroIdx χ T, (mult χ ρ.val : ℝ)) ≤
      T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) +
        0.5 * Real.log ((q : ℝ) * T) + 17.7 := by
  have e : (∑' ρ : ZeroIdx χ T, (mult χ ρ.val : ℝ)) =
      ∑ ρ ∈ (stripZeros_finite χ T).toFinset, (mult χ ρ : ℝ) :=
    tsum_zeroIdx χ T (fun z => (mult χ z : ℝ))
  rw [e]
  have h := (abs_le.mp (zero_count_two_sided_of_book hB χ hχ hT)).2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hl : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
  have he : 2 * bookMain q T =
      T / Real.pi * Real.log ((q : ℝ) * T / (2 * Real.pi * Real.exp 1)) := by
    unfold bookMain
    ring
  rw [he] at h
  unfold bookError at h
  linarith

end Count

set_option maxHeartbeats 800000 in
/-- PROVED, CONDITIONAL ON hB, the cited count of display 4.26, page 38. Unit shell count
for the tail of display 4.33, page 41. Same statement and proof as
`SplitGaussian123.tail_shell_count_le_quadratic`, with `strip_count_of_book`. -/
theorem tail_shell_count_le_quadratic_of_book (hB : MainHyps123.BookZeroCount)
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (T : ℝ) (n : ℕ) :
    (∑' ρ : {ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} // ⌊|ρ.val.im|⌋₊ = n},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val.val : ℝ)) ≤
        (2 * (q : ℝ) + 18) * ((n : ℝ) + 1) ^ 2 := by
  classical
  let I := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
    0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}
  let J := {ρ : I // ⌊|ρ.val.im|⌋₊ = n}
  let j : J → ZeroCount1623.ZeroIdx χ ((n : ℝ) + 1) := fun ρ =>
    ⟨ρ.val.val, ρ.val.property.1, ρ.val.property.2.1, ρ.val.property.2.2.1, by
      have h := Nat.lt_floor_add_one |ρ.val.val.im|
      rw [ρ.property] at h
      exact h.le⟩
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ZeroCount1623.ZeroIdx χ ((n : ℝ) + 1) => z.val) h
  haveI : Finite J := Finite.of_injective j hj
  have hs : Summable (fun ρ : J =>
      (ZeroCount1623.mult χ ρ.val.val : ℝ)) := Summable.of_finite
  have hc : (∑' ρ : J, (ZeroCount1623.mult χ ρ.val.val : ℝ)) ≤
      ∑' ρ : ZeroCount1623.ZeroIdx χ ((n : ℝ) + 1),
        (ZeroCount1623.mult χ ρ.val : ℝ) :=
    hs.tsum_le_tsum_of_inj j hj (fun _ _ => Nat.cast_nonneg _)
      (fun _ => le_rfl) (ZeroCount1623.summable_zeroIdx χ ((n : ℝ) + 1) _)
  have hU : 1 ≤ (n : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hU0 : 0 < (n : ℝ) + 1 := by positivity
  have hlog : log ((q : ℝ) * ((n : ℝ) + 1)) ≤ (q : ℝ) * ((n : ℝ) + 1) := by
    linarith only [log_le_sub_one_of_pos (mul_pos hq0 hU0)]
  have hratio : (q : ℝ) * ((n : ℝ) + 1) / (2 * π * exp 1) ≤
      (q : ℝ) * ((n : ℝ) + 1) := by
    apply div_le_self (by positivity)
    nlinarith only [pi_gt_three, Real.add_one_le_exp (1 : ℝ)]
  have hlogratio : log ((q : ℝ) * ((n : ℝ) + 1) / (2 * π * exp 1)) ≤
      (q : ℝ) * ((n : ℝ) + 1) :=
    (log_le_log (by positivity) hratio).trans hlog
  have hdiv : ((n : ℝ) + 1) / π ≤ (n : ℝ) + 1 :=
    div_le_self hU0.le (by linarith [pi_gt_three])
  have hmain : ((n : ℝ) + 1) / π *
      log ((q : ℝ) * ((n : ℝ) + 1) / (2 * π * exp 1)) ≤
        (q : ℝ) * ((n : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ (((n : ℝ) + 1) / π) * ((q : ℝ) * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hlogratio (by positivity)
      _ ≤ ((n : ℝ) + 1) * ((q : ℝ) * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hdiv (by positivity)
      _ = _ := by ring
  have hgrowth : 0 ≤ (q : ℝ) * (((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 1)) :=
    mul_nonneg hq0.le (by nlinarith only [hU])
  have hU2 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith only [hU]
  have hc' := strip_count_of_book hB χ hχ ((n : ℝ) + 1) hU
  change (∑' ρ : J, (ZeroCount1623.mult χ ρ.val.val : ℝ)) ≤ _
  exact hc.trans (hc'.trans (by nlinarith only [hmain, hlog, hgrowth, hU2]))

/-- PROVED, CONDITIONAL ON hB, the cited count of display 4.26, and on hcor, Corollary 3.2 at
k equal to 0, page 10. P0014 Lemma 4.5, page 41: the multiplicity weighted Mellin mass of
the zeros above height T is summable, for every shift. This is the summability half of
`SplitGaussian123.tail_mass_of_corollary`; no pairing is used. -/
theorem tail_mass_summable_of_book (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) := by
  have hT1 : 1 ≤ T := by have := (le_max_right _ _).trans hT; linarith
  have hs := tail_envelope_summable_of_shell_count χ δ T (2 * (q : ℝ) + 18) hT1
    (tail_shell_count_le_quadratic_of_book hB χ hχ T)
  apply (hs.mul_left 4.226).of_norm_bounded
  intro ρ
  rw [Real.norm_of_nonneg (by unfold mellinMassTerm; positivity)]
  calc
    _ ≤ _ := zero_mass_le_envelope χ δ T hT hcor ρ
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left (corEnvelope_le δ ρ.val.im)
        (show 0 ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) * 4.226
          by positivity)
      convert he using 1 <;> ring

/-- LEAF: P0014 Lemma 4.5, page 41, displays 4.33 to 4.35, the bound half of the zero sum
step, with the zero count of display 4.26 on page 38 given as hB and Corollary 3.2 at k equal
to 0 given as hcor. QUESTION, see notes/burst-20261120c/tail.md: the statement survives the
numeric screen at q = 1, but the paper's proof does not give it. Display 4.35 is false at
q = 1, T = 200, δ = 0, since page 38 drops the boundary term f(y) g(y) after display 4.28,
and the pairing of display 4.33 needs χ real. So this leaf needs a sharper Mellin bound than
hcor, not only the steps printed on page 41. -/
theorem tail_mass_bound_leaf (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) := by
  sorry

/-- SPLIT assembly, sorry free on its own, CONDITIONAL ON hB, the cited count of display
4.26 of P0014 page 38, and on the one LEAF `tail_mass_bound_leaf`. The exact sealed statement
of `SplitGaussian123.tail_mass_of_corollary`, P0014 Lemma 4.5, page 41, displays 4.33 to
4.35, with hB added. The summability half is PROVED from hB and hcor. -/
theorem tail_mass_of_corollary_of_book (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) :=
  ⟨tail_mass_summable_of_book hB q χ hχ δ T hT hcor,
    tail_mass_bound_leaf hB q χ hχ δ T hT hzeros hcor⟩

/-- Match check: with the open count leaf supplied for hB, the assembly has exactly the type
of the sealed `SplitGaussian123.tail_mass_of_corollary`. Depends on the open leaves. -/
example : type_of% @SplitGaussian123.tail_mass_of_corollary =
    type_of% (@tail_mass_of_corollary_of_book MainHyps123.book_zero_count_named_match) := rfl

end LeanLab.HelfgottMajor.MainTail123

#print axioms LeanLab.HelfgottMajor.MainTail123.tail_mass_summable_of_book
#print axioms LeanLab.HelfgottMajor.MainTail123.tail_mass_of_corollary_of_book
