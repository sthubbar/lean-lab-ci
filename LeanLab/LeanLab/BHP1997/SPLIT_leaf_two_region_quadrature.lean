/-
The E2 band of the section 5 lower density computation: the split of
`leaf_two_region_quadrature` of `DensitySlope517`, the quadrature of `1 / (a b^2)` over E2.

The target leaf asks for `13/10 ≤ ∫∫ 1 / (a b^2)` over E2. This file cuts it into

* three band inclusions, each a completely explicit set of rational linear inequalities and each
  contained in E2 with a margin of at least `2 * 10^-5`, far more than the allowed `ε ≤ 10^-8`:
  `leaf_high_band_membership` (the band `b ≥ 2273/10000`, where no case exclusion bites),
  `leaf_middle_band_membership` (the band below the line `4 a + 3 b = 15/8`) and
  `leaf_notch_band_membership` (the band above the line `4 a + 3 b = 17/8`, which straddles the
  excluded strip `15/8 < 4 a + 3 b < 17/8` by a disjunction);
* one quadrature, `leaf_three_band_quadrature`, of `1 / (a b^2)` over the union of the three
  bands: a rational function over an explicit polygon, with no `ε` and no case split of E2 in it
  (a floating point quadrature gives about 1.4963 there, and 1.4975 over E2 itself);
* one bound, `leaf_three_band_bound`, which is what the two fold monotonicity lemma needs.

The assembly `leaf_two_region_quadrature_split` only compares the two integrands pointwise, using
the three inclusions and the nonnegativity of `1 / (a b^2)` on E2.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DensitySlope517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

set_option maxHeartbeats 400000

/-- The union of the three bands is a measurable subset of the plane: a boolean combination of
closed half planes. -/
private lemma three_band_region_measurable :
    MeasurableSet {p : ℝ × ℝ | ((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧
            (p.1 + p.2 ≤ 7/16 ∨ 17/8 ≤ 4*p.1 + 5*p.2) ∧
            (2273/10000 ≤ p.1 ∨ p.1 + 1/8 ≤ 2*p.2)) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧
            (4*p.1 + p.2 ≤ 15/8 ∨ 17/8 ≤ 4*p.1 + p.2))) } := by
  have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
      MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
  simp only [Set.ofPred_and, Set.ofPred_or]
  repeat' first
    | apply MeasurableSet.inter
    | apply MeasurableSet.union
    | (apply hle <;> fun_prop)

/-- LEAF: first band inclusion. Every point with `b ≥ 2273/10000`, `b ≤ a ≤ 1/2` and
`9/16 ≤ a + 2 b ≤ 1` is in E2: the square `b ≤ a` already gives `4 a + 7 b ≥ 11 b ≥ 25003/10000`,
so the small `b` cut of the second alternative is killed, and `b ≥ 2273/10000 > 2272072/10^7`
kills both the third alternative and the last conjunct of the pair region. Only the strip cut
`a + 2 b ≥ 9/16 > 562492666/10^9` is used. -/
theorem leaf_high_band_membership {ε a b : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hb : 2273/10000 ≤ b) (hba : b ≤ a) (ha : a ≤ 1/2)
    (hs1 : 9/16 ≤ a + 2*b) (hs2 : a + 2*b ≤ 1) :
    lowerTwoDiscarded ε a b := by
  sorry

/-- LEAF: second band inclusion, the part of E2 below the strip `4 a + 3 b = 2`. Here
`4 a + 3 b ≤ 15/8` makes both `|4 a + 3 b - 2|` and `|4 a + b - 2|` at least `1/8`, which kills
the pair region, the strip cut `a + 2 b ≥ 9/16` kills the wide band, `17/8 ≤ 4 a + 7 b` kills the
first alternative and `a + b ≤ 7/16` or `17/8 ≤ 4 a + 5 b` kills the second; the last disjunct
keeps the point clear of the first alternative of the pair region. -/
theorem leaf_middle_band_membership {ε a b : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hb1 : 1/8 ≤ b) (hb2 : b ≤ 2273/10000) (hba : b ≤ a) (ha : a ≤ 1/2)
    (hs1 : 9/16 ≤ a + 2*b) (hs2 : a + 2*b ≤ 1)
    (hcut : 4*a + 3*b ≤ 15/8) (h7 : 17/8 ≤ 4*a + 7*b)
    (h5 : a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b)
    (hclear : 2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b) :
    lowerTwoDiscarded ε a b := by
  sorry

/-- LEAF: third band inclusion, the part of E2 above the strip `4 a + 3 b = 2`. Here
`17/8 ≤ 4 a + 3 b` kills the first and second alternatives at once, and forces
`a ≥ 3608/10000 > 2272072/10^7`, so the first alternative of the pair region fails; the
disjunction `4 a + b ≤ 15/8 ∨ 17/8 ≤ 4 a + b` is exactly the choice of the side of the other
excluded strip `4 a + b = 2`. -/
theorem leaf_notch_band_membership {ε a b : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hb1 : 1/8 ≤ b) (hb2 : b ≤ 2273/10000) (hba : b ≤ a) (ha : a ≤ 1/2)
    (hs1 : 9/16 ≤ a + 2*b) (hs2 : a + 2*b ≤ 1)
    (h3 : 17/8 ≤ 4*a + 3*b) (h4 : 4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b) :
    lowerTwoDiscarded ε a b := by
  sorry

/-- LEAF: the quadrature. The integral of `1 / (a b^2)` over the union of the three bands, as a
function of the plane, is at least `13/10`. The region is a fixed finite union of polygons cut out
by rational linear inequalities, so this is a computation about an explicit rational function; a
floating point quadrature gives about 1.4963, and an inner grid sum over cells inside the region
would prove it, in the same way as the certificate for the E2 sum. -/
theorem leaf_three_band_quadrature {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0 := by
  sorry

/-- LEAF: the pointwise bound the two fold monotonicity lemma needs. On the three bands
`1/8 ≤ b ≤ a` gives `a b^2 ≥ 1/512`, so the integrand is at most `512` there and zero elsewhere;
hence `10^3` bounds its absolute value everywhere. -/
theorem leaf_three_band_bound (a b : ℝ) :
    |(if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 := by
  sorry

/-- The E2 quadrature, assembled from the three band inclusions, the quadrature over their union
and the pointwise bound. Since every band is contained in E2 and `1 / (a b^2) ≥ 0` on E2, the
integrand of the union is pointwise at most the E2 integrand, and the two fold monotonicity lemma
`slope_two_mono` carries that to the integrals. -/
theorem leaf_two_region_quadrature_split {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0 := by
  have hle : ∀ a b : ℝ,
      (if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0) ≤
      (if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0) := by
    intro a b
    by_cases hR : (((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))))
    · rw [if_pos hR]
      rw [if_pos (by
        rcases hR with h | h | h
        · obtain ⟨hb, hba, ha, hs1, hs2⟩ := h
          exact leaf_high_band_membership hε hε8 hb hba ha hs1 hs2
        · obtain ⟨hb1, hb2, hba, ha, hs1, hs2, hcut, h7, h5, hclear⟩ := h
          exact leaf_middle_band_membership hε hε8 hb1 hb2 hba ha hs1 hs2 hcut h7 h5 hclear
        · obtain ⟨hb1, hb2, hba, ha, hs1, hs2, h3, h4⟩ := h
          exact leaf_notch_band_membership hε hε8 hb1 hb2 hba ha hs1 hs2 h3 h4)]
    · rw [if_neg hR]
      by_cases hD : lowerTwoDiscarded ε a b
      · rw [if_pos hD]
        obtain ⟨hb, hba, ha, hs⟩ := lower_two_domain_box hε8 hD
        have hb2 : (1/100:ℝ) ≤ b^2 := by nlinarith
        have hab : (1/10:ℝ)*(1/100) ≤ a*b^2 :=
          mul_le_mul (by linarith) hb2 (by norm_num) (by linarith)
        have hpos : 0 < a*b^2 := by linarith
        exact le_of_lt (one_div_pos.2 hpos)
      · rw [if_neg hD]
  have hf : Measurable (fun p : ℝ × ℝ =>
      if ((2273/10000 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧ p.1 + 2*p.2 ≤ 1) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 4*p.1 + 3*p.2 ≤ 15/8 ∧ 17/8 ≤ 4*p.1 + 7*p.2 ∧
            (p.1 + p.2 ≤ 7/16 ∨ 17/8 ≤ 4*p.1 + 5*p.2) ∧
            (2273/10000 ≤ p.1 ∨ p.1 + 1/8 ≤ 2*p.2)) ∨
        (1/8 ≤ p.2 ∧ p.2 ≤ 2273/10000 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1/2 ∧ 9/16 ≤ p.1 + 2*p.2 ∧
            p.1 + 2*p.2 ≤ 1 ∧ 17/8 ≤ 4*p.1 + 3*p.2 ∧
            (4*p.1 + p.2 ≤ 15/8 ∨ 17/8 ≤ 4*p.1 + p.2))) then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite three_band_region_measurable (by fun_prop) measurable_const
  have hg : Measurable (fun p : ℝ × ℝ =>
      if lowerTwoDiscarded ε p.1 p.2 then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite (two_density_region_measurable ε) (by fun_prop) measurable_const
  have hfb : ∀ a b : ℝ, |(if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)| ≤ 1000 :=
    fun a b => leaf_three_band_bound a b
  have hgb : ∀ a b : ℝ,
      |(if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0)| ≤ 1000 := fun a b => by
    by_cases hD : lowerTwoDiscarded ε a b
    · simp only [hD, ↓reduceIte]
      obtain ⟨hb, hba, ha, hs⟩ := lower_two_domain_box hε8 hD
      have hb2 : (1/100:ℝ) ≤ b^2 := by nlinarith
      have hab : (1/10:ℝ)*(1/100) ≤ a*b^2 :=
        mul_le_mul (by linarith) hb2 (by norm_num) (by linarith)
      have hpos : 0 < a*b^2 := by linarith
      have h1 : 1/(a*b^2) ≤ 1000 := by rw [div_le_iff₀ hpos]; linarith
      have h0 : 0 ≤ 1/(a*b^2) := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
    · simp only [hD, ↓reduceIte]
      norm_num
  have hmono := slope_two_mono
    (fun a b => if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0)
    (fun a b => if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0)
    hf hg (M := 1000) hfb hgb hle (lo := 1/10) (hi := 1/2) (by norm_num)
  have hq := leaf_three_band_quadrature hε hε8
  linarith

end LeanLab.BHP1997.LowerShortC165
