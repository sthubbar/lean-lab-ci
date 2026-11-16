/-
P0069 page 51. The existing three conservative band inclusions and their bound.
Four declarations moved unchanged from SPLIT_leaf_two_region_quadrature.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165dBase312
import LeanLab.BHP1997.BandQuadrature635

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- LEAF: first band inclusion. Every point with `b ≥ 2273/10000`, `b ≤ a ≤ 1/2` and
`9/16 ≤ a + 2 b ≤ 1` is in E2: the square `b ≤ a` already gives `4 a + 7 b ≥ 11 b ≥ 25003/10000`,
so the small `b` cut of the second alternative is killed, and `b ≥ 2273/10000 > 2272072/10^7`
kills both the third alternative and the last conjunct of the pair region. Only the strip cut
`a + 2 b ≥ 9/16 > 562492666/10^9` is used. -/
theorem leaf_high_band_membership {ε a b : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hb : 2273/10000 ≤ b) (hba : b ≤ a) (ha : a ≤ 1/2)
    (hs1 : 9/16 ≤ a + 2*b) (hs2 : a + 2*b ≤ 1) :
    lowerTwoDiscarded ε a b := by
  unfold lowerTwoDiscarded upperPairRegion
  refine ⟨by linarith, hba, ha, hs2, ?_⟩
  rintro (hA | hB | hC | hD)
  · linarith
  · linarith
  · linarith
  · obtain ⟨-, -, -, hbD, -⟩ := hD
    linarith

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
  unfold lowerTwoDiscarded upperPairRegion
  refine ⟨by linarith, hba, ha, hs2, ?_⟩
  rintro (hA | hB | hC | hD)
  · linarith
  · linarith
  · rcases h5 with h5 | h5 <;> linarith
  · obtain ⟨-, -, -, -, hrest⟩ := hD
    rcases hrest with ⟨h1, h2⟩ | h3 | h4
    · rcases hclear with hcl | hcl
      · linarith
      · linarith
    · rw [abs_le] at h3
      linarith
    · rw [abs_le] at h4
      linarith

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
  unfold lowerTwoDiscarded upperPairRegion
  refine ⟨by linarith, hba, ha, hs2, ?_⟩
  rintro (hA | hB | hC | hD)
  · linarith
  · linarith
  · linarith
  · obtain ⟨-, -, -, -, hrest⟩ := hD
    rcases hrest with ⟨h1, h2⟩ | h5 | h5
    · linarith
    · rw [abs_le] at h5
      linarith
    · rcases h4 with h4 | h4 <;> rw [abs_le] at h5 <;> linarith

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
  split_ifs with h
  · have hb1 : (1/8:ℝ) ≤ b := by
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · linarith
      · exact h1
      · exact h1
    have hba : b ≤ a := by
      rcases h with ⟨-, h2, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, h2, -⟩
      · exact h2
      · exact h2
      · exact h2
    have hb2 : (1/64:ℝ) ≤ b^2 := by nlinarith
    have hmul : (1/8:ℝ)*(1/64) ≤ a*b^2 :=
      mul_le_mul (le_trans hb1 hba) hb2 (by norm_num) (by linarith)
    have hpos : 0 < a*b^2 := by linarith
    have hnn : 0 ≤ (1:ℝ)/(a*b^2) := by positivity
    rw [abs_of_nonneg hnn]
    rw [div_le_iff₀ hpos]
    linarith
  · norm_num

end LeanLab.BHP1997.LowerShortC165
