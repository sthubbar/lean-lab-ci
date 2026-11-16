/-
P0069, Section 5, pages 50 and 51, displays 5.15 and 5.17.
The E4 exponent integrand, mixed quadratures and elementary support bounds.
The four coordinate estimates are proved in FourExponentQuadrature517.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.FourDensityMain517a
import LeanLab.BHP1997.FourExponentMesh517
import LeanLab.BHP1997.FourExponentCells517
import LeanLab.BHP1997.FourExponentBoundary517
import LeanLab.BHP1997.FourExponentRegularity517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- Page 51 display 5.17. The zero extended E4 density integrand. -/
noncomputable def fourExponentKernel (ω : ℝ → ℝ) (ε s a b c d : ℝ) : ℝ :=
  if lowerFourRegion ε a b c d then
    (if (s-a-b-c-d)/d < 1 then 0 else ω ((s-a-b-c-d)/d)/(a*b*c*d^2))
  else 0

/-- Page 51 display 5.17. The mixed quadratures after zero to four innermost
integer variables have been replaced by their exponent integrals.
The fourth stage is the paper density. -/
noncomputable def fourExponentMixed (ω : ℝ → ℝ) (ε x s : ℝ) (k : ℕ) : ℝ :=
  let B := Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊
  let w := fun n : ℕ => 1 / ((n : ℝ) * Real.log (scaleZ ε x))
  let e := expo ε x
  let l := lowerFourGridReal 0
  let u := lowerFourGridReal 128
  match k with
  | 0 => ∑ i ∈ (B ×ˢ B ×ˢ B ×ˢ B).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
        i.2.1 < i.1 ∧ i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
          lowerFourRegion ε (e i.1) (e i.2.1) (e i.2.2.1) (e i.2.2.2)),
      fourExponentKernel ω ε s (e i.1) (e i.2.1) (e i.2.2.1) (e i.2.2.2) *
        (w i.1 * w i.2.1 * w i.2.2.1 * w i.2.2.2)
  | 1 => ∑ a ∈ B, ∑ b ∈ B, ∑ c ∈ B,
      if b < a ∧ c < b then
        (∫ d in l..u, fourExponentKernel ω ε s (e a) (e b) (e c) d) *
          (w a * w b * w c)
      else 0
  | 2 => ∑ a ∈ B, ∑ b ∈ B,
      if b < a then
        (∫ c in l..u, ∫ d in l..u, fourExponentKernel ω ε s (e a) (e b) c d) *
          (w a * w b)
      else 0
  | 3 => ∑ a ∈ B,
      (∫ b in l..u, ∫ c in l..u, ∫ d in l..u,
        fourExponentKernel ω ε s (e a) b c d) * w a
  | _ => lowerFourDensityAt ω ε s

/-- Page 51 display 5.17. The entire E4 region lies inside the actual
integration box, including the lower endpoint margin in epsilon. -/
theorem four_exponent_region_grid_box {ε a b c d : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hr : lowerFourRegion ε a b c d) :
    (lowerFourGridReal 0 ≤ a ∧ a ≤ lowerFourGridReal 128) ∧
      (lowerFourGridReal 0 ≤ b ∧ b ≤ lowerFourGridReal 128) ∧
      (lowerFourGridReal 0 ≤ c ∧ c ≤ lowerFourGridReal 128) ∧
      (lowerFourGridReal 0 ≤ d ∧ d ≤ lowerFourGridReal 128) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  norm_num [lowerFourGridReal, lowerFourGridPoint] at h1 h5 hε8 ⊢
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

/-- Page 51 display 5.17. A strict ordered point remains in the E4 region. -/
theorem four_exponent_region_instance :
    lowerFourRegion (1/10^9) (143/1000) (285/2000) (71/500) (283/2000) := by
  norm_num [lowerFourRegion, lowerFourCovered, upperPrimeCovered, upperPairRegion, abs_le]

/-- Page 51 display 5.17. Shifting the grid by one removes the zero
index and gives a strictly increasing exponent grid. -/
theorem four_exponent_shifted_grid_strict {ε x : ℝ} (hZ : 1 < scaleZ ε x) :
    StrictMono (fun n : ℕ => expo ε x (n+1)) := by
  intro m n hmn
  unfold expo
  apply (div_lt_div_iff_of_pos_right (Real.log_pos hZ)).mpr
  exact Real.log_lt_log (by positivity) (by exact_mod_cast Nat.succ_lt_succ hmn)

/-- Page 51 display 5.17. The remaining normalized harmonic weights have
bounded total mass, independently of the number of integer indices. -/
theorem four_exponent_weight_mass {Z : ℝ} (hZ : 1 < Z) (hL : 1 ≤ Real.log Z)
    (N : ℕ) (hN : (N : ℝ) ≤ Z) :
    ∑ n ∈ Finset.Icc 1 N, 1 / ((n : ℝ) * Real.log Z) ≤ 2 := by
  by_cases hN0 : N = 0
  · subst N
    simp
  have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hlog := Real.log_le_log hNp hN
  have hsum : (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa only [one_div] using h
  have hL0 : 0 < Real.log Z := Real.log_pos hZ
  calc _ = (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n) / Real.log Z := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro n _
        rw [div_div]
    _ ≤ (1 + Real.log N) / Real.log Z := div_le_div_of_nonneg_right hsum hL0.le
    _ ≤ 2 := (div_le_iff₀ hL0).mpr (by linarith)

/-- Page 51 display 5.17 with the lab scale Z equal to four Y. On the
short dyadic integer interval the density parameter lies between zero and one. -/
theorem four_exponent_short_range {ε x : ℝ} (hε : 0 < ε) (hx : 1 ≤ x)
    {m : ℕ} (hm1 : ⌊x ^ (11 / 20 + ε)⌋₊ < m)
    (hm2 : m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊) :
    0 ≤ Real.log (m : ℝ) / Real.log (scaleZ ε x) ∧
      Real.log (m : ℝ) / Real.log (scaleZ ε x) ≤ 1 := by
  have hY : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
  have hZ : 1 < scaleZ ε x := by unfold scaleZ shortY; linarith
  have hL : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm1
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
  have hmY : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    (by exact_mod_cast hm2 : (m : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)).trans
      (Nat.floor_le (by positivity))
  have hmZ : (m : ℝ) ≤ scaleZ ε x := by unfold scaleZ shortY; linarith
  refine ⟨div_nonneg (Real.log_nonneg hmone) hL.le, ?_⟩
  exact (div_le_one hL).mpr (Real.log_le_log hmp hmZ)

/-- Page 51 display 5.17. On the nonzero side of the Buchstab jump the
actual E4 kernel is uniformly Lipschitz in its last exponent. -/
theorem four_exponent_kernel_coordinate_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s a b c d e : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hrd : lowerFourRegion ε a b c d) (hre : lowerFourRegion ε a b c e)
    (hu : 1 ≤ (s-a-b-c-d)/d) (hv : 1 ≤ (s-a-b-c-e)/e) :
    |fourExponentKernel ω ε s a b c d - fourExponentKernel ω ε s a b c e| ≤
      60000000 * |d-e| := by
  obtain ⟨hd, hdc, hcb, hba, hd1, hsum⟩ := Decomp514a.four_density_region_box hε hε8 hrd
  obtain ⟨he, hec, _, _, he1, _⟩ := Decomp514a.four_density_region_box hε hε8 hre
  have ha : (1/10 : ℝ) ≤ a := by linarith
  have hb : (1/10 : ℝ) ≤ b := by linarith
  have hc : (1/10 : ℝ) ≤ c := by linarith
  have hT : |s-a-b-c| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have h := four_exponent_density_coordinate_d hω hz hT ha hb hc hd he
    (by linarith) (by linarith) hu hv
  simpa only [fourExponentKernel, if_pos hrd, if_pos hre,
    if_neg (not_lt.mpr hu), if_neg (not_lt.mpr hv)] using h

#print axioms four_exponent_region_grid_box
#print axioms four_exponent_region_instance
#print axioms four_exponent_shifted_grid_strict
#print axioms four_exponent_weight_mass
#print axioms four_exponent_short_range
#print axioms four_exponent_kernel_coordinate_d
end LeanLab.BHP1997.LowerShortC165
