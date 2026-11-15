/-
P0069 Baker, Harman and Pintz 1997, Section 5, pages 51 and 52, the U-1624 normalization:
the lab factor moves by at most `1 / (2 Y)` between neighbouring integers of J, from the slope
leaf and a Lipschitz leaf for the density `V(s)` near `s = 1`.
No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LowerPrincipal517a

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51, the integrals of display 5.17 and of `v0`, with the U-1624
normalization of pages 51 and 52. The density `V(s) = 1/s - D2(s) - D4(s)` of the raw
coefficient is Lipschitz just below `s = 1`: the Buchstab function is bounded and Lipschitz
on `[1, ∞)`, its jump at one is crossed only on a strip of area `O(|s - s'|)`, and the
integrands are bounded on the boxes. This is a lab normalization fact about the page 51
integrals, not a printed formula. -/
theorem leaf_density_lipschitz (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ s0 L : ℝ, s0 < 1 ∧ ∀ s s' : ℝ, s0 ≤ s → s ≤ 1 → s0 ≤ s' → s' ≤ 1 →
      |lowerDensityAt ω ε s - lowerDensityAt ω ε s'| ≤ L * |s - s'| := by
  obtain ⟨L2, δ2, hL2, hδ2, h2⟩ := Decomp514a.two_density_lipschitz ω hω hz hε hε8
  obtain ⟨L4, δ4, hL4, hδ4, h4⟩ := Decomp514a.four_density_lipschitz ω hω hz hε hε8
  refine ⟨max (1 / 2) (max (1 - δ2) (1 - δ4)), 4 + L2 + L4, ?_, fun s s' hs hs1 hs' hs1' => ?_⟩
  · exact max_lt (by norm_num) (max_lt (by linarith) (by linarith))
  have hsh : (1 / 2 : ℝ) ≤ s := (le_max_left _ _).trans hs
  have hsh' : (1 / 2 : ℝ) ≤ s' := (le_max_left _ _).trans hs'
  have hs2 : 1 - δ2 ≤ s := ((le_max_left _ _).trans (le_max_right _ _)).trans hs
  have hs2' : 1 - δ2 ≤ s' := ((le_max_left _ _).trans (le_max_right _ _)).trans hs'
  have hs4 : 1 - δ4 ≤ s := ((le_max_right _ _).trans (le_max_right _ _)).trans hs
  have hs4' : 1 - δ4 ≤ s' := ((le_max_right _ _).trans (le_max_right _ _)).trans hs'
  have e2 := h2 s s' hs2 hs1 hs2' hs1'
  have e4 := h4 s s' hs4 hs1 hs4' hs1'
  have hpos : 0 < s := by linarith
  have hpos' : 0 < s' := by linarith
  have e1 : |1 / s - 1 / s'| ≤ 4 * |s - s'| := by
    have hss : 0 < s * s' := mul_pos hpos hpos'
    have hq : (1 / 4 : ℝ) ≤ s * s' := by nlinarith
    rw [div_sub_div _ _ hpos.ne' hpos'.ne', abs_div, abs_of_pos hss, div_le_iff₀ hss,
      one_mul, mul_one, abs_sub_comm s' s]
    nlinarith [abs_nonneg (s - s')]
  unfold lowerDensityAt
  have key : 1 / s - lowerTwoDensityAt ω ε s - lowerFourDensityAt ω ε s -
      (1 / s' - lowerTwoDensityAt ω ε s' - lowerFourDensityAt ω ε s') =
      (1 / s - 1 / s') - (lowerTwoDensityAt ω ε s - lowerTwoDensityAt ω ε s') -
        (lowerFourDensityAt ω ε s - lowerFourDensityAt ω ε s') := by ring
  rw [key]
  have t1 := abs_sub (1 / s - 1 / s' - (lowerTwoDensityAt ω ε s - lowerTwoDensityAt ω ε s'))
    (lowerFourDensityAt ω ε s - lowerFourDensityAt ω ε s')
  have t2 := abs_sub (1 / s - 1 / s') (lowerTwoDensityAt ω ε s - lowerTwoDensityAt ω ε s')
  nlinarith [abs_nonneg (s - s')]

/-- P0069 pages 51 and 52 with the U-1624 normalization, the step behind display 5.17 on
page 51: for large `x` and every integer `m` from floor Y to floor 2Y the exponent
`s = log m / log Z` lies in the range of the slope bound, the density `V(s)` is at least
`v0`, and the clipping of the lab factor is inactive, so the factor is exactly
`v0 log Z / (log Y * V(s))`. -/
theorem factor_unclipped_near_one (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) {s0 : ℝ} (hs0 : s0 < 1)
    (hpos : 0 < lowerV0 ω ε)
    (hV : ∀ s : ℝ, s0 ≤ s → s ≤ 1 →
      lowerV0 ω ε * (1 + 3 * (1 - s)) ≤ lowerDensityAt ω ε s) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      s0 ≤ Real.log m / Real.log (scaleZ ε x) ∧ Real.log m / Real.log (scaleZ ε x) ≤ 1 ∧
      lowerV0 ω ε ≤ lowerDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) ∧
      lowerFactor ω ε x m = lowerV0 ω ε * Real.log (scaleZ ε x) /
        (Real.log (x ^ (11 / 20 + ε)) *
          lowerDensityAt ω ε (Real.log m / Real.log (scaleZ ε x))) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  refine ⟨Real.exp (2 * max (4 * Real.log 2) (3 * Real.log 2 / (1 - s0))), fun x hx m hm1 hm2 => ?_⟩
  have hK1 : 4 * Real.log 2 ≤ max (4 * Real.log 2) (3 * Real.log 2 / (1 - s0)) := le_max_left _ _
  have hK2 : 3 * Real.log 2 / (1 - s0) ≤ max (4 * Real.log 2) (3 * Real.log 2 / (1 - s0)) :=
    le_max_right _ _
  generalize max (4 * Real.log 2) (3 * Real.log 2 / (1 - s0)) = K at hx hK1 hK2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 2 * K ≤ Real.log x := by
    rw [← Real.log_exp (2 * K)]; exact Real.log_le_log (Real.exp_pos _) hx
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hLY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x := Real.log_rpow hx0 _
  have hLYK : K ≤ Real.log (x ^ (11 / 20 + ε)) := by rw [hLY]; nlinarith
  have hLZ : Real.log (scaleZ ε x) = 2 * Real.log 2 + Real.log (x ^ (11 / 20 + ε)) := by
    unfold scaleZ shortY; rw [Real.log_mul (by norm_num) hY0.ne', h4]
  have hY2 : 2 ≤ x ^ (11 / 20 + ε) := by
    rw [← Real.log_le_log_iff (by norm_num) hY0]; linarith
  have hfl : x ^ (11 / 20 + ε) < (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmr : (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm1
  have hmY : x ^ (11 / 20 + ε) / 2 ≤ (m : ℝ) := by linarith
  have hm2' : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    (Nat.cast_le.mpr hm2).trans (Nat.floor_le (by positivity))
  have hm0 : 0 < (m : ℝ) := by linarith
  have hLm1 : Real.log (x ^ (11 / 20 + ε)) - Real.log 2 ≤ Real.log m := by
    rw [← Real.log_div hY0.ne' (by norm_num)]; exact Real.log_le_log (by positivity) hmY
  have hLm2 : Real.log m ≤ Real.log 2 + Real.log (x ^ (11 / 20 + ε)) := by
    rw [← Real.log_mul (by norm_num) hY0.ne']; exact Real.log_le_log hm0 hm2'
  unfold lowerFactor
  rw [hLZ]
  generalize Real.log (x ^ (11 / 20 + ε)) = LY at *
  generalize Real.log (m : ℝ) = Lm at *
  generalize Real.log 2 = l at *
  have hLYpos : 0 < LY := by nlinarith
  have hLZpos : 0 < 2 * l + LY := by positivity
  have hs0' : 0 < 1 - s0 := by linarith
  have hK2' : 3 * l ≤ LY * (1 - s0) := by
    have := hK2.trans hLYK
    rwa [div_le_iff₀ hs0'] at this
  have hs1 : s0 ≤ Lm / (2 * l + LY) := by
    rw [le_div_iff₀ hLZpos]; nlinarith
  have hs2 : Lm / (2 * l + LY) ≤ 1 := by
    rw [div_le_one hLZpos]; linarith
  have hs := hV _ hs1 hs2
  have he : l / (2 * l + LY) ≤ 1 - Lm / (2 * l + LY) := by
    rw [show 1 - Lm / (2 * l + LY) = (2 * l + LY - Lm) / (2 * l + LY) by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hLZpos.le
  refine ⟨hs1, hs2, ?_⟩
  generalize lowerDensityAt ω ε (Lm / (2 * l + LY)) = V at *
  have hV' : lowerV0 ω ε * (1 + 3 * (l / (2 * l + LY))) ≤ V := by nlinarith
  have hpos1 : 0 < 1 + 3 * (l / (2 * l + LY)) := by positivity
  have hVpos : 0 < V := lt_of_lt_of_le (mul_pos hpos hpos1) hV'
  have hq : 2 * l + LY ≤ LY * (1 + 3 * (l / (2 * l + LY))) := by
    rw [show LY * (1 + 3 * (l / (2 * l + LY))) = LY * (2 * l + LY + 3 * l) / (2 * l + LY) by
      field_simp]
    rw [le_div_iff₀ hLZpos]; nlinarith
  have hnum : lowerV0 ω ε * (2 * l + LY) ≤ LY * V := by
    calc lowerV0 ω ε * (2 * l + LY) ≤ lowerV0 ω ε * (LY * (1 + 3 * (l / (2 * l + LY)))) :=
          mul_le_mul_of_nonneg_left hq hpos.le
      _ = LY * (lowerV0 ω ε * (1 + 3 * (l / (2 * l + LY)))) := by ring
      _ ≤ LY * V := mul_le_mul_of_nonneg_left hV' hLYpos.le
  have hR1 : lowerV0 ω ε * (2 * l + LY) / (LY * V) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hnum
  have hR0 : 0 ≤ lowerV0 ω ε * (2 * l + LY) / (LY * V) := by positivity
  refine ⟨?_, ?_⟩
  · have h3 : 0 ≤ l / (2 * l + LY) := by positivity
    nlinarith
  · rw [min_eq_right hR1, max_eq_right hR0]

/-- P0069 page 51 display 5.17 after partial summation against the lab factor: the local
increment bound of the factor on the integer interval from floor Y to floor 2Y, the same
statement as `Decomp514a.leaf_factor_increment`. CONDITIONAL on the open leaves
`leaf_density_slope` and `leaf_density_lipschitz`. -/
theorem factor_increment_of_density (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → 1 ≤ x →
      ∀ i ∈ Finset.Ico ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |lowerFactor ω ε x (i + 1) - lowerFactor ω ε x i| ≤
          1 / (2 * x ^ (11 / 20 + ε)) := by
  obtain ⟨hv0, s1, hs1, hV⟩ := leaf_density_slope ω hω hz hε hε8
  obtain ⟨s2, L, hs2, hLip⟩ := leaf_density_lipschitz ω hω hz hε hε8
  rcases hv0.eq_or_lt with h0 | hpos
  · refine ⟨0, fun x _ hx1 i _ => ?_⟩
    have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
    have hF : ∀ m : ℕ, lowerFactor ω ε x m = 0 := by
      intro m; unfold lowerFactor; simp [← h0]
    rw [hF, hF, sub_zero, abs_zero]; positivity
  have hs0 : max s1 s2 < 1 := max_lt hs1 hs2
  obtain ⟨C0, hC0⟩ := factor_unclipped_near_one ω hε hs0 hpos
    (fun s h1 h2 => hV s ((le_max_left _ _).trans h1) h2)
  refine ⟨max C0 (Real.exp (2 * max (Real.log 2) (4 * max L 0 / lowerV0 ω ε))),
    fun x hx _ i hi => ?_⟩
  have hxC : C0 ≤ x := (le_max_left _ _).trans hx
  have hxe := (le_max_right _ _).trans hx
  have hK1 := le_max_left (Real.log 2) (4 * max L 0 / lowerV0 ω ε)
  have hK2 := le_max_right (Real.log 2) (4 * max L 0 / lowerV0 ω ε)
  generalize max (Real.log 2) (4 * max L 0 / lowerV0 ω ε) = K at hxe hK1 hK2
  have hL0 : 0 ≤ max L 0 := le_max_right _ _
  have hLip' : ∀ s s' : ℝ, max s1 s2 ≤ s → s ≤ 1 → max s1 s2 ≤ s' → s' ≤ 1 →
      |lowerDensityAt ω ε s - lowerDensityAt ω ε s'| ≤ max L 0 * |s - s'| :=
    fun s s' a b c d =>
      (hLip s s' ((le_max_right _ _).trans a) b ((le_max_right _ _).trans c) d).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  generalize max L 0 = L' at hK2 hL0 hLip'
  rw [Finset.mem_Ico] at hi
  obtain ⟨a1, a2, a3, a4⟩ := hC0 x hxC i hi.1 hi.2.le
  obtain ⟨b1, b2, b3, b4⟩ := hC0 x hxC (i + 1) (hi.1.trans (Nat.le_succ _)) hi.2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hlogx : 2 * K ≤ Real.log x := by
    rw [← Real.log_exp (2 * K)]; exact Real.log_le_log (Real.exp_pos _) hxe
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hLY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x := Real.log_rpow hx0 _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLYK : K ≤ Real.log (x ^ (11 / 20 + ε)) := by rw [hLY]; nlinarith
  have hY2 : 2 ≤ x ^ (11 / 20 + ε) := by
    rw [← Real.log_le_log_iff (by norm_num) hY0]; linarith
  have hLZpos : 0 < Real.log (scaleZ ε x) :=
    Real.log_pos (by unfold scaleZ shortY; linarith)
  have hfl : x ^ (11 / 20 + ε) < (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hir : (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr hi.1
  have hiY : x ^ (11 / 20 + ε) / 2 ≤ (i : ℝ) := by linarith
  have hi0 : 0 < (i : ℝ) := by linarith
  have hd0 : 0 ≤ Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ) := by
    rw [sub_nonneg]; exact Real.log_le_log hi0 (by push_cast; linarith)
  have hd1 : Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ) ≤ 2 / x ^ (11 / 20 + ε) := by
    rw [← Real.log_div (by positivity) hi0.ne']
    have h1 := Real.log_le_sub_one_of_pos (show 0 < ((i + 1 : ℕ) : ℝ) / (i : ℝ) by positivity)
    have h2 : ((i + 1 : ℕ) : ℝ) / (i : ℝ) - 1 = 1 / (i : ℝ) := by
      push_cast; field_simp; ring
    have h3 : 1 / (i : ℝ) ≤ 2 / x ^ (11 / 20 + ε) := by
      rw [div_le_div_iff₀ hi0 hY0]; linarith
    linarith
  have hds : |Real.log (i : ℝ) / Real.log (scaleZ ε x) -
      Real.log ((i + 1 : ℕ) : ℝ) / Real.log (scaleZ ε x)| ≤
      2 / x ^ (11 / 20 + ε) / Real.log (scaleZ ε x) := by
    rw [abs_sub_comm, ← sub_div, abs_of_nonneg (div_nonneg hd0 hLZpos.le)]
    exact div_le_div_of_nonneg_right hd1 hLZpos.le
  have hlip := hLip' _ _ a1 a2 b1 b2
  rw [b4, a4]
  generalize Real.log (x ^ (11 / 20 + ε)) = LY at *
  generalize x ^ (11 / 20 + ε) = Y at *
  generalize Real.log (scaleZ ε x) = a at *
  generalize lowerDensityAt ω ε (Real.log (i : ℝ) / a) = V1 at *
  generalize lowerDensityAt ω ε (Real.log ((i + 1 : ℕ) : ℝ) / a) = V2 at *
  generalize lowerV0 ω ε = v at *
  have hLYpos : 0 < LY := by linarith
  have hV1 : 0 < V1 := hpos.trans_le a3
  have hV2 : 0 < V2 := hpos.trans_le b3
  have hK2' : 4 * L' ≤ LY * v := by
    have := hK2.trans hLYK
    rwa [div_le_iff₀ hpos] at this
  have hVV : |V1 - V2| ≤ L' * (2 / Y / a) :=
    hlip.trans (mul_le_mul_of_nonneg_left hds hL0)
  have heq : v * a / (LY * V2) - v * a / (LY * V1) = v * a / (LY * V1 * V2) * (V1 - V2) := by
    field_simp
  have hc0 : 0 ≤ v * a / (LY * V1 * V2) := by positivity
  have hc1 : v * a / (LY * V1 * V2) ≤ v * a / (LY * v * v) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have h5 : v * v ≤ V1 * V2 := mul_le_mul a3 b3 hpos.le hV1.le
    have h6 := mul_le_mul_of_nonneg_left h5 hLYpos.le
    linarith
  rw [heq, abs_mul, abs_of_nonneg hc0]
  have e1 : v * a / (LY * V1 * V2) * |V1 - V2| ≤ v * a / (LY * v * v) * (L' * (2 / Y / a)) :=
    mul_le_mul hc1 hVV (abs_nonneg _) (by positivity)
  have e2 : v * a / (LY * v * v) * (L' * (2 / Y / a)) = 2 * L' / (LY * v * Y) := by
    field_simp
  have e3 : 2 * L' / (LY * v * Y) ≤ 1 / (2 * Y) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 := mul_le_mul_of_nonneg_right hK2' hY0.le
    linarith
  linarith

end LeanLab.BHP1997.LowerShortC165
