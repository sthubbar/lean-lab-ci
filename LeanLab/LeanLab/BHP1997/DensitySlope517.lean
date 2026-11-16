/-
P0069 Baker, Harman and Pintz 1997, Section 5, pages 51 and 52, display 5.17 and the lab
normalization of the density `V(s)` of the raw lower coefficient near `s = 1`.

Target: `leaf_density_slope` of LowerPrincipal517a, `0 ≤ v0` and
`v0 (1 + 3 (1 - s)) ≤ V(s)` just below `s = 1`. This file proves it from

* the certified page 51 upper bound `E2 integral ≤ 3799/4000`, taken here as a hypothesis so
  that this file does not import the heavy certificate; `DensitySlope517b` supplies it;
* `leaf_two_region_quadrature`, the integral of `1 / (a b^2)` over E2 is at least `13/10`;
* `leaf_two_variation_quadrature`, the integral over E2 of an explicit majorant of the upward
  variation of the E2 integrand between `s` and one is at most 2.

Both leaves are free of the Buchstab function: they are quadratures of explicit rational
functions over the polygon E2.

The E4 part, `four_density_drop`, the loss of the strip `s < a + 2 b ≤ 1` of E2,
`two_density_strip_pointwise`, and the measure theory, `slope_strip_generic`, are proved here. No new definition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.BandRegion635

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d Decomp514a
open scoped BigOperators

set_option maxHeartbeats 400000

/-- P0069 page 51, display 5.17, the Buchstab function of the E2 and E4 integrals: `ω ≥ 1/2`
on `[1, ∞)`. On `[1, 2]` it is `1 / u`; beyond, `u ω(u)` has derivative `ω(u - 1) ≥ 1/2`. -/
theorem buchstab_half_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {u : ℝ} (hu : 1 ≤ u) : 1/2 ≤ ω u := by
  have step : ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ)+2 → 1/2 ≤ ω u := by
    intro n
    induction n with
    | zero =>
      intro u hu hu2
      have hu0 : 0 < u := by linarith
      have hu2' : u ≤ 2 := by simpa using hu2
      rw [hω.2.1 u hu hu2', div_le_div_iff₀ (by norm_num) hu0]
      linarith
    | succ n ih =>
      intro u hu huMax
      push_cast at huMax
      by_cases hsmall : u ≤ (n : ℝ)+2
      · exact ih u hu hsmall
      have hb2 : (2:ℝ) ≤ (n:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbu : (n:ℝ)+2 ≤ u := (lt_of_not_ge hsmall).le
      have hwb : 1/2 ≤ ω ((n:ℝ)+2) := ih _ (by linarith) le_rfl
      have hcont : ContinuousOn (fun t : ℝ => t*ω t) (Set.Icc ((n:ℝ)+2) u) :=
        continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
      have hci : ContinuousOn (fun t : ℝ => ω (t-1)) (Set.uIcc ((n:ℝ)+2) u) := by
        rw [Set.uIcc_of_le hbu]
        apply hω.1.comp (by fun_prop)
        intro t ht
        change 1 ≤ t-1
        linarith [ht.1]
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hbu hcont
        (fun t ht => hω.2.2 t (by linarith [ht.1])) hci.intervalIntegrable
      have hI : (u - ((n:ℝ)+2)) * (1/2) ≤ ∫ t in ((n:ℝ)+2)..u, ω (t-1) := by
        have hm := intervalIntegral.integral_mono_on hbu
          (intervalIntegrable_const (c := (1/2:ℝ)) (μ := MeasureTheory.volume))
          hci.intervalIntegrable
          (fun t ht => ih (t-1) (by linarith [ht.1]) (by linarith [ht.2]))
        rw [intervalIntegral.integral_const, smul_eq_mul] at hm
        exact hm
      have hu0 : 0 < u := by linarith
      have huω : u * (1/2) ≤ u*ω u := by nlinarith
      exact le_of_mul_le_mul_left huω hu0
  exact step ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])

open MeasureTheory Set in
/-- P0069 page 51 display 5.17. One level of the nested E4 integral: two jointly measurable
bounded integrands in pointwise order have parametric interval integrals in the same order. -/
theorem slope_level_mono {α : Type*} [MeasurableSpace α] (φ ψ : α → ℝ → ℝ)
    (hφ : Measurable (fun p : α × ℝ => φ p.1 p.2))
    (hψ : Measurable (fun p : α × ℝ => ψ p.1 p.2)) {M : ℝ}
    (hφM : ∀ x y, |φ x y| ≤ M) (hψM : ∀ x y, |ψ x y| ≤ M)
    (hle : ∀ x y, φ x y ≤ ψ x y) {lo hi : ℝ} (h : lo ≤ hi) (x : α) :
    (∫ y in lo..hi, φ x y) ≤ ∫ y in lo..hi, ψ x y := by
  have hint : ∀ χ : α → ℝ → ℝ, Measurable (fun p : α × ℝ => χ p.1 p.2) →
      (∀ x y, |χ x y| ≤ M) → IntervalIntegrable (χ x) volume lo hi := by
    intro χ hχ hχM
    have hmx : Measurable (χ x) := hχ.comp measurable_prodMk_left
    have hb : ∀ s : Set ℝ, ∀ᵐ y ∂(volume.restrict s), ‖χ x y‖ ≤ M :=
      fun s => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hχM x y
    exact ⟨Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmx.aestronglyMeasurable
        (hb _),
      Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmx.aestronglyMeasurable (hb _)⟩
  exact intervalIntegral.integral_mono_on h (hint φ hφ hφM) (hint ψ hψ hψM)
    (fun y _ => hle x y)

/-- P0069 page 51 display 5.17. Four nested levels: two jointly measurable bounded integrands
on four space in pointwise order have fourfold iterated integrals in the same order. -/
theorem slope_nested_mono (f g : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hf : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ => f p.1.1.1 p.1.1.2 p.1.2 p.2))
    (hg : Measurable (fun p : ((ℝ × ℝ) × ℝ) × ℝ => g p.1.1.1 p.1.1.2 p.1.2 p.2))
    {M : ℝ} (hfM : ∀ a b c d, |f a b c d| ≤ M) (hgM : ∀ a b c d, |g a b c d| ≤ M)
    (hle : ∀ a b c d, f a b c d ≤ g a b c d) {lo hi : ℝ} (h : lo ≤ hi) :
    (∫ a in lo..hi, ∫ b in lo..hi, ∫ c in lo..hi, ∫ d in lo..hi, f a b c d) ≤
      ∫ a in lo..hi, ∫ b in lo..hi, ∫ c in lo..hi, ∫ d in lo..hi, g a b c d := by
  have f1 := four_density_level (fun (q : (ℝ × ℝ) × ℝ) d => f q.1.1 q.1.2 q.2 d) hf
    (fun q d => hfM _ _ _ _) lo hi
  have g1 := four_density_level (fun (q : (ℝ × ℝ) × ℝ) d => g q.1.1 q.1.2 q.2 d) hg
    (fun q d => hgM _ _ _ _) lo hi
  have m1 := slope_level_mono (fun (q : (ℝ × ℝ) × ℝ) d => f q.1.1 q.1.2 q.2 d)
    (fun (q : (ℝ × ℝ) × ℝ) d => g q.1.1 q.1.2 q.2 d) hf hg
    (fun q d => hfM _ _ _ _) (fun q d => hgM _ _ _ _) (fun q d => hle _ _ _ _) h
  have f2 := four_density_level
    (fun (r : ℝ × ℝ) c => ∫ d in lo..hi, f r.1 r.2 c d) f1.1 (fun r c => f1.2 (r, c)) lo hi
  have g2 := four_density_level
    (fun (r : ℝ × ℝ) c => ∫ d in lo..hi, g r.1 r.2 c d) g1.1 (fun r c => g1.2 (r, c)) lo hi
  have m2 := slope_level_mono
    (fun (r : ℝ × ℝ) c => ∫ d in lo..hi, f r.1 r.2 c d)
    (fun (r : ℝ × ℝ) c => ∫ d in lo..hi, g r.1 r.2 c d) f1.1 g1.1
    (fun r c => f1.2 (r, c)) (fun r c => g1.2 (r, c)) (fun r c => m1 (r, c)) h
  have f3 := four_density_level
    (fun (a : ℝ) b => ∫ c in lo..hi, ∫ d in lo..hi, f a b c d) f2.1
    (fun a b => f2.2 (a, b)) lo hi
  have g3 := four_density_level
    (fun (a : ℝ) b => ∫ c in lo..hi, ∫ d in lo..hi, g a b c d) g2.1
    (fun a b => g2.2 (a, b)) lo hi
  have m3 := slope_level_mono
    (fun (a : ℝ) b => ∫ c in lo..hi, ∫ d in lo..hi, f a b c d)
    (fun (a : ℝ) b => ∫ c in lo..hi, ∫ d in lo..hi, g a b c d) f2.1 g2.1
    (fun a b => f2.2 (a, b)) (fun a b => g2.2 (a, b)) (fun a b => m2 (a, b)) h
  exact slope_level_mono
    (fun (_ : Unit) a => ∫ b in lo..hi, ∫ c in lo..hi, ∫ d in lo..hi, f a b c d)
    (fun (_ : Unit) a => ∫ b in lo..hi, ∫ c in lo..hi, ∫ d in lo..hi, g a b c d)
    (f3.1.comp measurable_snd) (g3.1.comp measurable_snd)
    (fun _ a => f3.2 a) (fun _ a => g3.2 a) (fun _ a => m3 a) h ()

/-- P0069 page 51 display 5.17, the E4 integral with `1` replaced by `s`: pointwise on the
region E4 the integrand at `s ∈ [99/100, 1]` is at most `1 + 20 (1 - s)` times the integrand
at one, since `ω` is 1-Lipschitz and at least `1/2` on `[1, ∞)` and the fourth exponent is at
least `1/10`. -/
theorem four_density_pointwise_drop {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {s : ℝ} (hs : 99/100 ≤ s) (hs1 : s ≤ 1)
    (a b c d : ℝ) :
    (if lowerFourRegion ε a b c d then
        (if (s-a-b-c-d)/d < 1 then 0 else ω ((s-a-b-c-d)/d)/(a*b*c*d^2))
      else 0) ≤
      (1 + 20*(1-s)) * (if lowerFourRegion ε a b c d then
        (if (1-a-b-c-d)/d < 1 then 0 else ω ((1-a-b-c-d)/d)/(a*b*c*d^2))
      else 0) := by
  by_cases hR : lowerFourRegion ε a b c d
  · simp only [hR, ↓reduceIte]
    obtain ⟨hd, hdc, hcb, hba, hd18, hsum⟩ := four_density_region_box hε hε8 hR
    have hd0 : 0 < d := by linarith
    have hu : 1 ≤ (s-a-b-c-d)/d := by rw [one_le_div hd0]; linarith
    have hu' : 1 ≤ (1-a-b-c-d)/d := by rw [one_le_div hd0]; linarith
    simp only [not_lt.2 hu, not_lt.2 hu', ↓reduceIte]
    have hpos : 0 < a*b*c*d^2 := by
      have ha0 : 0 < a := by linarith
      have hb0 : 0 < b := by linarith
      have hc0 : 0 < c := by linarith
      positivity
    have huu : (s-a-b-c-d)/d ≤ (1-a-b-c-d)/d :=
      div_le_div_of_nonneg_right (by linarith) hd0.le
    have hL := four_density_buchstab_lipschitz_ordered hω hz hu huu
    have hdiff : (1-a-b-c-d)/d - (s-a-b-c-d)/d = (1-s)/d := by field_simp; ring
    rw [hdiff] at hL
    have hq : (1-s)/d ≤ 10*(1-s) := by
      rw [div_le_iff₀ hd0]
      nlinarith [mul_nonneg (sub_nonneg.2 hs1) (by linarith : (0:ℝ) ≤ d - 1/10)]
    have hhalf := buchstab_half_le hω hu'
    have hL1 := (abs_le.1 hL).2
    have hnum : ω ((s-a-b-c-d)/d) ≤ (1 + 20*(1-s)) * ω ((1-a-b-c-d)/d) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hs1)
        (by linarith : (0:ℝ) ≤ ω ((1-a-b-c-d)/d) - 1/2)]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hnum hpos.le
  · simp only [hR, ↓reduceIte]
    simp

/-- P0069 page 51 display 5.17, the E4 integral with `1` replaced by `s`: for
`s ∈ [99/100, 1]` it is at most `1 + 20 (1 - s)` times the printed E4 integral. -/
theorem four_density_drop {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {s : ℝ} (hs : 99/100 ≤ s) (hs1 : s ≤ 1) :
    lowerFourDensityAt ω ε s ≤ (1 + 20*(1-s)) * lowerFourDensityAt ω ε 1 := by
  have hc0 : 0 ≤ 1 + 20*(1-s) := by linarith
  have hc1 : 1 + 20*(1-s) ≤ 2 := by linarith
  have h := slope_nested_mono
    (fun a b c d => if lowerFourRegion ε a b c d then
        (if (s-a-b-c-d)/d < 1 then 0 else ω ((s-a-b-c-d)/d)/(a*b*c*d^2)) else 0)
    (fun a b c d => (1 + 20*(1-s)) * (if lowerFourRegion ε a b c d then
        (if (1-a-b-c-d)/d < 1 then 0 else ω ((1-a-b-c-d)/d)/(a*b*c*d^2)) else 0))
    (four_density_integrand_measurable hω hz ε s)
    ((four_density_integrand_measurable hω hz ε 1).const_mul (1 + 20*(1-s)))
    (M := 2 * 10^5)
    (fun a b c d => (four_density_integrand_bound hω hz hε hε8 s a b c d).trans (by norm_num))
    (fun a b c d => by
      have hb := four_density_integrand_bound hω hz hε hε8 1 a b c d
      rw [abs_mul, abs_of_nonneg hc0]
      nlinarith [abs_nonneg (if lowerFourRegion ε a b c d then
        (if (1-a-b-c-d)/d < 1 then 0 else ω ((1-a-b-c-d)/d)/(a*b*c*d^2)) else 0)])
    (fun a b c d => four_density_pointwise_drop hω hz hε hε8 hs hs1 a b c d)
    (lo := lowerFourGridReal 0) (hi := lowerFourGridReal 128)
    (by norm_num [lowerFourGridReal, lowerFourGridPoint])
  unfold lowerFourDensityAt
  refine h.trans (le_of_eq ?_)
  simp only [intervalIntegral.integral_const_mul]

/-- P0069 page 51, display 5.17, the Buchstab function of the E2 integral beyond its minimum at
two: for `2 ≤ u ≤ v` it drops by at most `(7/200) (v - u)`. By the mean value theorem for
`w ω(w)`, whose derivative `ω(w - 1)` is at least `1/2`, and `ω(u) ≤ 0.567144`. -/
theorem buchstab_drop_high {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) : ω u - ω v ≤ 7/200*(v-u) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · simp
  have hc : ContinuousOn (fun w : ℝ => w * ω w) (Set.Icc u v) :=
    continuousOn_id.mul (hω.1.mono (fun w hw => by
      have := hw.1
      simp only [Set.mem_Ici]; linarith))
  obtain ⟨c, hcm, hce⟩ := exists_hasDerivAt_eq_slope (fun w : ℝ => w * ω w)
    (fun w : ℝ => ω (w - 1)) hlt hc
    (fun w hw => hω.2.2 w (by have := hw.1; linarith))
  have hvu : 0 < v - u := by linarith
  have hce' : ω (c - 1) * (v - u) = v * ω v - u * ω u := by
    rw [hce]; field_simp
  have hC := buchstab_half_le hω (show 1 ≤ c - 1 by have := hcm.1; linarith)
  have hU := LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_567144 hω hu
  have hv0 : 0 < v := by linarith
  have hk : v * (ω u - ω v) ≤ v * (7/200*(v-u)) := by
    nlinarith [mul_nonneg hvu.le
        (by linarith : (0:ℝ) ≤ 567144/1000000 - ω u + (ω (c-1) - 1/2)),
      mul_nonneg hvu.le (by linarith : (0:ℝ) ≤ v - 2)]
  exact le_of_mul_le_mul_left hk hv0

/-- P0069 page 51 display 5.17. Two nested levels: two jointly measurable bounded integrands
on the plane in pointwise order have twofold iterated integrals in the same order. -/
theorem slope_two_mono (f g : ℝ → ℝ → ℝ)
    (hf : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hg : Measurable (fun p : ℝ × ℝ => g p.1 p.2))
    {M : ℝ} (hfM : ∀ a b, |f a b| ≤ M) (hgM : ∀ a b, |g a b| ≤ M)
    (hle : ∀ a b, f a b ≤ g a b) {lo hi : ℝ} (h : lo ≤ hi) :
    (∫ a in lo..hi, ∫ b in lo..hi, f a b) ≤ ∫ a in lo..hi, ∫ b in lo..hi, g a b := by
  have f1 := four_density_level f hf hfM lo hi
  have g1 := four_density_level g hg hgM lo hi
  have m1 := slope_level_mono f g hf hg hfM hgM hle h
  exact slope_level_mono
    (fun (_ : Unit) a => ∫ b in lo..hi, f a b) (fun (_ : Unit) a => ∫ b in lo..hi, g a b)
    (f1.1.comp measurable_snd) (g1.1.comp measurable_snd)
    (fun _ a => f1.2 a) (fun _ a => g1.2 a) (fun _ a => m1 a) h ()

/-- LEAF: P0069 page 51, the set E2 of the computer calculation that gives `v0`, a numeric
lower bound free of the Buchstab function. The integral of `1 / (a b^2)` over E2 is at least
`13/10`. A floating point quadrature gives about 1.4975, so the margin is about 0.197; an inner
grid sum over cells inside E2 would prove it. -/
theorem leaf_two_region_quadrature {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0 := by

  have hband_measurable :
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
    Measurable.ite hband_measurable (by fun_prop) measurable_const
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
  have hq := three_band_quadrature635 hε hε8
  linarith

/-- P0069 page 51, the E2 integral of the computer calculation that gives `v0`, a lower bound:
the integral of `ω((1 - a - b)/b) / (a b^2)` over E2 is at least `13/20`, since `ω ≥ 1/2` on
`[1, ∞)` by `buchstab_half_le`. A floating point quadrature gives about 0.9373. CONDITIONAL on
`leaf_two_region_quadrature`. -/
theorem two_density_lower (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/20 ≤ lowerTwoDeletedIntegral ω ε := by
  have hq := leaf_two_region_quadrature hε hε8
  have hgeo : Measurable (fun p : ℝ × ℝ =>
      if lowerTwoDiscarded ε p.1 p.2 then 1/(p.1*p.2^2) else 0) :=
    Measurable.ite (two_density_region_measurable ε) (by fun_prop) measurable_const
  have hm := slope_two_mono
    (fun a b => (1/2) * (if lowerTwoDiscarded ε a b then 1/(a*b^2) else 0))
    (fun a b => if lowerTwoDiscarded ε a b then ω ((1-a-b)/b)/(a*b^2) else 0)
    (hgeo.const_mul (1/2)) (two_density_integrand_measurable hω hz ε 1) (M := 1000)
    (fun a b => by
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
        norm_num)
    (fun a b => by
      have hb := two_density_integrand_bound hω hz hε8 1 a b
      rw [abs_of_nonneg hb.1]; exact hb.2)
    (fun a b => by
      by_cases hD : lowerTwoDiscarded ε a b
      · simp only [hD, ↓reduceIte]
        obtain ⟨hb, hba, ha, hs⟩ := lower_two_domain_box hε8 hD
        have hb0 : 0 < b := by linarith
        have ha0 : 0 < a := by linarith
        have hP : 0 < a*b^2 := by positivity
        have hu1 : 1 ≤ (1-a-b)/b := by rw [one_le_div hb0]; linarith
        rw [← mul_div_assoc, mul_one]
        exact div_le_div_of_nonneg_right (buchstab_half_le hω hu1) hP.le
      · simp only [hD, ↓reduceIte]
        norm_num)
    (lo := 1/10) (hi := 1/2) (by norm_num)
  simp only [intervalIntegral.integral_const_mul] at hm
  have h21 : lowerTwoDensityAt ω ε 1 = lowerTwoDeletedIntegral ω ε := rfl
  rw [← h21]
  unfold lowerTwoDensityAt
  linarith

open MeasureTheory Set in
/-- P0069 page 51 display 5.17. One level of a nested density integral: a jointly measurable
bounded integrand is interval integrable in its last variable. -/
theorem slope_level_integrable {α : Type*} [MeasurableSpace α] (φ : α → ℝ → ℝ)
    (hφ : Measurable (fun p : α × ℝ => φ p.1 p.2)) {M : ℝ} (hφM : ∀ x y, |φ x y| ≤ M)
    (lo hi : ℝ) (x : α) : IntervalIntegrable (φ x) volume lo hi := by
  have hmx : Measurable (φ x) := hφ.comp measurable_prodMk_left
  have hb : ∀ s : Set ℝ, ∀ᵐ y ∂(volume.restrict s), ‖φ x y‖ ≤ M :=
    fun s => Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hφM x y
  exact ⟨Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmx.aestronglyMeasurable
      (hb _),
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmx.aestronglyMeasurable (hb _)⟩

open MeasureTheory Set in
/-- P0069 page 51 display 5.17. A nonnegative integrable function that is at least `c` on a
subinterval `(x, y]` has integral at least `c (y - x)`. -/
theorem slope_slice_lower {F : ℝ → ℝ} {lo hi x y c : ℝ}
    (hF : IntervalIntegrable F volume lo hi) (h0 : ∀ b, 0 ≤ F b)
    (hc : ∀ b ∈ Ioc x y, c ≤ F b) (hlx : lo ≤ x) (hxy : x ≤ y) (hyh : y ≤ hi) :
    c * (y - x) ≤ ∫ b in lo..hi, F b := by
  have hlh : lo ≤ hi := hlx.trans (hxy.trans hyh)
  have hFi : IntegrableOn F (Ioc lo hi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlh).1 hF
  have hsub : Ioc x y ⊆ Ioc lo hi := Ioc_subset_Ioc hlx hyh
  have h1 : (∫ _b in x..y, c) = c * (y - x) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [intervalIntegral.integral_of_le hxy] at h1
  rw [intervalIntegral.integral_of_le hlh, ← h1]
  calc (∫ _b in Ioc x y, c) ≤ ∫ b in Ioc x y, F b :=
        setIntegral_mono_on (continuous_const.integrableOn_Ioc) (hFi.mono_set hsub)
          measurableSet_Ioc hc
    _ ≤ ∫ b in Ioc lo hi, F b :=
        setIntegral_mono_set hFi (Filter.Eventually.of_forall h0)
          (Filter.Eventually.of_forall fun b hb => hsub hb)

open MeasureTheory Set in
/-- P0069 page 51 display 5.17, the E2 integral with `1` replaced by `s`, measure theory of the
comparison of two densities. If `G1 - Gs ≥ c` on a strip of height `w` over `(A1, A2]`, then
the twofold integral of `G1` exceeds that of `Gs` by at least `c w (A2 - A1)` minus the
integral of the positive part of `Gs - G1`. -/
theorem slope_strip_generic (G1 Gs : ℝ → ℝ → ℝ)
    (h1m : Measurable (fun p : ℝ × ℝ => G1 p.1 p.2))
    (hsm : Measurable (fun p : ℝ × ℝ => Gs p.1 p.2))
    {M : ℝ} (h1b : ∀ a b, 0 ≤ G1 a b ∧ G1 a b ≤ M) (hsb : ∀ a b, 0 ≤ Gs a b ∧ Gs a b ≤ M)
    {lo hi A1 A2 c w : ℝ} (hlo : lo ≤ A1) (hA : A1 ≤ A2) (hhi : A2 ≤ hi) (hw : 0 ≤ w)
    (X : ℝ → ℝ) (hX : ∀ a ∈ Ioc A1 A2, lo ≤ X a ∧ X a + w ≤ hi)
    (hstrip : ∀ a ∈ Ioc A1 A2, ∀ b ∈ Ioc (X a) (X a + w), c ≤ G1 a b - Gs a b) :
    c * w * (A2 - A1) - (∫ a in lo..hi, ∫ b in lo..hi, max (Gs a b - G1 a b) 0) ≤
      (∫ a in lo..hi, ∫ b in lo..hi, G1 a b) - ∫ a in lo..hi, ∫ b in lo..hi, Gs a b := by
  have hlh : lo ≤ hi := hlo.trans (hA.trans hhi)
  have hPm : Measurable (fun p : ℝ × ℝ => max (Gs p.1 p.2 - G1 p.1 p.2) 0) :=
    (hsm.sub h1m).max measurable_const
  have a1 : ∀ a b, |G1 a b| ≤ M := fun a b => by
    rw [abs_of_nonneg (h1b a b).1]; exact (h1b a b).2
  have as : ∀ a b, |Gs a b| ≤ M := fun a b => by
    rw [abs_of_nonneg (hsb a b).1]; exact (hsb a b).2
  have aP : ∀ a b, |max (Gs a b - G1 a b) 0| ≤ M := fun a b => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [(hsb a b).2, (h1b a b).1]) ((hsb a b).1.trans (hsb a b).2)
  have i1 : ∀ a, IntervalIntegrable (fun b => G1 a b) volume lo hi :=
    fun a => slope_level_integrable G1 h1m a1 lo hi a
  have is' : ∀ a, IntervalIntegrable (fun b => Gs a b) volume lo hi :=
    fun a => slope_level_integrable Gs hsm as lo hi a
  have iP : ∀ a, IntervalIntegrable (fun b => max (Gs a b - G1 a b) 0) volume lo hi :=
    fun a => slope_level_integrable (fun a b => max (Gs a b - G1 a b) 0) hPm aP lo hi a
  have iD : ∀ a, IntervalIntegrable (fun b => G1 a b - Gs a b) volume lo hi :=
    fun a => (i1 a).sub (is' a)
  have iF : ∀ a, IntervalIntegrable
      (fun b => G1 a b - Gs a b + max (Gs a b - G1 a b) 0) volume lo hi :=
    fun a => (iD a).add (iP a)
  have l1 := four_density_level G1 h1m a1 lo hi
  have ls := four_density_level Gs hsm as lo hi
  have lP := four_density_level (fun a b => max (Gs a b - G1 a b) 0) hPm aP lo hi
  have o1 : IntervalIntegrable (fun a => ∫ b in lo..hi, G1 a b) volume lo hi :=
    slope_level_integrable (fun (_ : Unit) a => ∫ b in lo..hi, G1 a b)
      (l1.1.comp measurable_snd) (fun _ a => l1.2 a) lo hi ()
  have os : IntervalIntegrable (fun a => ∫ b in lo..hi, Gs a b) volume lo hi :=
    slope_level_integrable (fun (_ : Unit) a => ∫ b in lo..hi, Gs a b)
      (ls.1.comp measurable_snd) (fun _ a => ls.2 a) lo hi ()
  have oP : IntervalIntegrable (fun a => ∫ b in lo..hi, max (Gs a b - G1 a b) 0)
      volume lo hi :=
    slope_level_integrable (fun (_ : Unit) a => ∫ b in lo..hi, max (Gs a b - G1 a b) 0)
      (lP.1.comp measurable_snd) (fun _ a => lP.2 a) lo hi ()
  have oD : IntervalIntegrable
      (fun a => (∫ b in lo..hi, G1 a b) - ∫ b in lo..hi, Gs a b) volume lo hi := o1.sub os
  have oK : IntervalIntegrable
      (fun a => (∫ b in lo..hi, G1 a b) - (∫ b in lo..hi, Gs a b) +
        ∫ b in lo..hi, max (Gs a b - G1 a b) 0) volume lo hi := oD.add oP
  have hin : ∀ a, (∫ b in lo..hi, (G1 a b - Gs a b + max (Gs a b - G1 a b) 0)) =
      (∫ b in lo..hi, G1 a b) - (∫ b in lo..hi, Gs a b) +
        ∫ b in lo..hi, max (Gs a b - G1 a b) 0 := fun a =>
    (intervalIntegral.integral_add (iD a) (iP a)).trans
      (congrArg (fun t => t + ∫ b in lo..hi, max (Gs a b - G1 a b) 0)
        (intervalIntegral.integral_sub (i1 a) (is' a)))
  have hF0 : ∀ a b, 0 ≤ G1 a b - Gs a b + max (Gs a b - G1 a b) 0 := fun a b => by
    linarith [le_max_left (Gs a b - G1 a b) 0]
  have hK0 : ∀ a, 0 ≤ (∫ b in lo..hi, G1 a b) - (∫ b in lo..hi, Gs a b) +
      ∫ b in lo..hi, max (Gs a b - G1 a b) 0 := fun a => by
    rw [← hin a]; exact intervalIntegral.integral_nonneg hlh (fun b _ => hF0 a b)
  have hKc : ∀ a ∈ Ioc A1 A2, c * w ≤ (∫ b in lo..hi, G1 a b) - (∫ b in lo..hi, Gs a b) +
      ∫ b in lo..hi, max (Gs a b - G1 a b) 0 := fun a ha => by
    rw [← hin a]
    have h := slope_slice_lower (iF a) (hF0 a)
      (fun b hb => by
        show c ≤ G1 a b - Gs a b + max (Gs a b - G1 a b) 0
        linarith [hstrip a ha b hb, le_max_right (Gs a b - G1 a b) 0])
      (hX a ha).1 (by linarith : X a ≤ X a + w) (hX a ha).2
    have e : c * (X a + w - X a) = c * w := by ring
    rw [e] at h
    exact h
  have hout := slope_slice_lower oK hK0 hKc hlo hA hhi
  have e1 := intervalIntegral.integral_add oD oP
  have e2 := intervalIntegral.integral_sub o1 os
  rw [e1, e2] at hout
  linarith

/-- P0069 page 51, the set E2 and display 5.17: for `a ∈ (1/3, 1/2]` and `s ∈ [99/100, 1]` the
points with `s < a + 2 b ≤ 1` lie in E2; there the Buchstab argument `(s - a - b)/b` is below
one, so the integrand at `s` vanishes, while the integrand at one is
`1 / (a b (1 - a - b)) ≥ 26`. -/
theorem two_density_strip_pointwise {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {s : ℝ} (hs : 99/100 ≤ s)
    {a b : ℝ} (ha : a ∈ Set.Ioc (1/3:ℝ) (1/2))
    (hb : b ∈ Set.Ioc ((s-a)/2) ((s-a)/2 + (1-s)/2)) :
    26 ≤ (if lowerTwoDiscarded ε a b then ω ((1-a-b)/b)/(a*b^2) else 0) -
      (if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hε8' : ε ≤ 1/100000000 := hε8.trans (by norm_num)
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hD : lowerTwoDiscarded ε a b := by
    unfold lowerTwoDiscarded upperPairRegion
    refine ⟨by norm_num; linarith, by linarith, ha2, by linarith, ?_⟩
    rintro (h | ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, h, -⟩) <;> norm_num at h <;> linarith
  simp only [hD, ↓reduceIte]
  have hus : (s-a-b)/b < 1 := by rw [div_lt_one hb0]; linarith
  rw [hz _ hus, zero_div, sub_zero]
  have hu1 : 1 ≤ (1-a-b)/b := by rw [one_le_div hb0]; linarith
  have hu2 : (1-a-b)/b ≤ 2 := by rw [div_le_iff₀ hb0]; linarith
  rw [hω.2.1 _ hu1 hu2, one_div_div]
  have hg : 0 < 1-a-b := by linarith
  have hpoly : a*((1-a)/2)*((1-a)/2+1/200) ≤ 1/26 := by
    nlinarith [mul_nonneg (sq_nonneg (a-1/3)) (by linarith : (0:ℝ) ≤ 4/3 - a),
      sq_nonneg (a-1/2)]
  have h1 : a*b ≤ a*((1-a)/2) := mul_le_mul_of_nonneg_left (by linarith) ha0.le
  have h2 : a*b*(1-a-b) ≤ a*((1-a)/2)*((1-a)/2+1/200) :=
    mul_le_mul h1 (by linarith) hg.le (mul_nonneg ha0.le (by linarith))
  have h3 : 26*(a*b*(1-a-b)) ≤ 1 := by linarith
  rw [le_div_iff₀ (by positivity : 0 < a*b^2), le_div_iff₀ hg]
  nlinarith [mul_le_mul_of_nonneg_left h3 hb0.le]

/-- P0069 page 51, the set E2: the explicit majorant of the upward variation of the E2
integrand lies between 0 and `10^4`. -/
theorem two_variation_bound {ε : ℝ} (hε8 : ε ≤ 1/10^8) (a b : ℝ) :
    0 ≤ (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0) ∧
    (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0) ≤ 10^4 := by
  by_cases hD : lowerTwoDiscarded ε a b
  · simp only [hD, ↓reduceIte]
    obtain ⟨hb, hba, ha, hsum⟩ := lower_two_domain_box hε8 hD
    have hb0 : 0 < b := by linarith
    have ha0 : 0 < a := by linarith
    have hq : 0 < 1-a-b := by linarith
    have hr : 0 < 99/100-a-b := by linarith
    have hb3 : (1/10:ℝ)^3 ≤ b^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have hab3 : (1/10:ℝ)*(1/10)^3 ≤ a*b^3 :=
      mul_le_mul (by linarith) hb3 (by norm_num) ha0.le
    have hpos3 : 0 < a*b^3 := by positivity
    have h4 : (1/10:ℝ)*(1/10)*(1/10)*(1/10) ≤ a*b*(99/100-a-b)*(1-a-b) :=
      mul_le_mul (mul_le_mul (mul_le_mul (by linarith) (by linarith) (by norm_num) ha0.le)
        (by linarith) (by norm_num) (mul_pos ha0 hb0).le) (by linarith) (by norm_num)
        (mul_pos (mul_pos ha0 hb0) hr).le
    have hpos4 : 0 < a*b*(99/100-a-b)*(1-a-b) := mul_pos (mul_pos (mul_pos ha0 hb0) hr) hq
    split_ifs
    · refine ⟨div_nonneg zero_le_one hpos4.le, ?_⟩
      rw [div_le_iff₀ hpos4]; linarith
    · refine ⟨div_nonneg (by norm_num) hpos3.le, ?_⟩
      rw [div_le_iff₀ hpos3]; linarith
    · refine ⟨div_nonneg (by norm_num) hpos3.le, ?_⟩
      rw [div_le_iff₀ hpos3]; linarith
  · simp only [hD, ↓reduceIte]
    norm_num

/-- P0069 page 51, display 5.17 for the E2 sum, the integral with `1` replaced by `s`,
pointwise. For `s ∈ [99/100, 1]` the positive part of the E2 integrand at `s` minus the E2
integrand at one is at most `1 - s` times an explicit function free of `ω`. On the strip
`s < a + 2 b` the integrand at `s` vanishes. Where both Buchstab arguments are at most two,
`ω(u) = 1/u` gives `(1 - s) / (a b (s - a - b) (1 - a - b))`. Where both are at least two,
`buchstab_drop_high` gives the factor `7/200`; in between the two bounds add up to at most
`107/200`. -/
theorem two_density_variation_pointwise {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε8 : ε ≤ 1/10^8) {s : ℝ} (hs : 99/100 ≤ s) (hs1 : s ≤ 1) (a b : ℝ) :
    max ((if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) -
        (if lowerTwoDiscarded ε a b then ω ((1-a-b)/b)/(a*b^2) else 0)) 0 ≤
      (1-s) * (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0) := by
  have hδ : 0 ≤ 1 - s := by linarith
  have hR0 := (two_variation_bound hε8 a b).1
  refine max_le ?_ (mul_nonneg hδ hR0)
  by_cases hD : lowerTwoDiscarded ε a b
  · simp only [hD, ↓reduceIte] at hR0 ⊢
    obtain ⟨hb, hba, ha, hsum⟩ := lower_two_domain_box hε8 hD
    have hb0 : 0 < b := by linarith
    have ha0 : 0 < a := by linarith
    have hP : 0 < a*b^2 := by positivity
    have hq : 0 < 1-a-b := by linarith
    have hr : 0 < 99/100-a-b := by linarith
    have hu1 : 1 ≤ (1-a-b)/b := by rw [one_le_div hb0]; linarith
    have hω1 := two_density_buchstab_nonneg hω hz ((1-a-b)/b)
    by_cases hstrip : s < a+2*b
    · have hus : (s-a-b)/b < 1 := by rw [div_lt_one hb0]; linarith
      rw [hz _ hus, zero_div, zero_sub]
      have h0 : 0 ≤ ω ((1-a-b)/b)/(a*b^2) := div_nonneg hω1 hP.le
      linarith [mul_nonneg hδ hR0]
    · have hsab : a+2*b ≤ s := not_lt.1 hstrip
      have hp : 0 < s-a-b := by linarith
      have hp' : s-a-b ≠ 0 := hp.ne'
      have hq' : 1-a-b ≠ 0 := hq.ne'
      have hus : 1 ≤ (s-a-b)/b := by rw [one_le_div hb0]; linarith
      have hdiff : (1-a-b)/b - (s-a-b)/b = (1-s)/b := by field_simp; ring
      have fin : ∀ K : ℝ, ω ((s-a-b)/b) - ω ((1-a-b)/b) ≤ K*((1-s)/b) →
          ω ((s-a-b)/b)/(a*b^2) - ω ((1-a-b)/b)/(a*b^2) ≤ (1-s)*(K/(a*b^3)) := by
        intro K hK
        have e : (1-s)*(K/(a*b^3)) = (K*((1-s)/b))/(a*b^2) := by field_simp
        rw [e, ← sub_div]
        exact div_le_div_of_nonneg_right hK hP.le
      by_cases h1 : 1 ≤ a+3*b
      · simp only [h1, ↓reduceIte]
        have hu2 : (1-a-b)/b ≤ 2 := by rw [div_le_iff₀ hb0]; linarith
        have hus2 : (s-a-b)/b ≤ 2 := by rw [div_le_iff₀ hb0]; linarith
        rw [hω.2.1 _ hus hus2, hω.2.1 _ hu1 hu2, one_div_div, one_div_div]
        have e : b/(s-a-b)/(a*b^2) - b/(1-a-b)/(a*b^2) =
            (1-s)*(1/(a*b*(s-a-b)*(1-a-b))) := by
          field_simp
          ring
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ hδ
        refine one_div_le_one_div_of_le (mul_pos (mul_pos (mul_pos ha0 hb0) hr) hq) ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (mul_pos ha0 hb0).le) hq.le
      · have h1' : a+3*b < 1 := not_le.1 h1
        have hu2 : 2 ≤ (1-a-b)/b := by rw [le_div_iff₀ hb0]; linarith
        simp only [h1, ↓reduceIte]
        by_cases h2 : a+3*b ≤ s
        · have hus2 : 2 ≤ (s-a-b)/b := by rw [le_div_iff₀ hb0]; linarith
          have hdrop := buchstab_drop_high hω hus2
            (div_le_div_of_nonneg_right (by linarith : s-a-b ≤ 1-a-b) hb0.le)
          rw [hdiff] at hdrop
          have hq0 : 0 ≤ (1-s)/b := div_nonneg hδ hb0.le
          split_ifs
          · exact fin _ (by linarith)
          · exact fin _ hdrop
        · have h2' : s < a+3*b := not_le.1 h2
          have h99 : (99/100:ℝ) ≤ a+3*b := by linarith
          simp only [h99, ↓reduceIte]
          have hus2 : (s-a-b)/b ≤ 2 := by rw [div_le_iff₀ hb0]; linarith
          have hdrop := buchstab_drop_high hω le_rfl hu2
          rw [hω.2.1 2 (by norm_num) le_rfl] at hdrop
          apply fin
          rw [hω.2.1 _ hus hus2]
          have hus0 : 0 < (s-a-b)/b := by linarith
          have hinv : 1/((s-a-b)/b) - 1/2 ≤ (1/2)*(2 - (s-a-b)/b) := by
            rw [div_sub_div _ _ hus0.ne' two_ne_zero, div_le_iff₀ (by positivity)]
            nlinarith [mul_nonneg (sub_nonneg.2 hus) (sub_nonneg.2 hus2)]
          linarith
  · simp only [hD, ↓reduceIte]
    norm_num

/-- LEAF: P0069 page 51, the set E2, a numeric upper bound free of the Buchstab function for
the majorant of `two_density_variation_pointwise`: its integral over the box is at most 2.
A floating point quadrature gives about 1.70: about 1.49 from `a + 3 b ≥ 1`, about 0.06 from
`99/100 ≤ a + 3 b < 1` and about 0.14 from `a + 3 b < 99/100`. An outer grid sum over cells
meeting E2 would prove it. -/
theorem leaf_two_variation_quadrature {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0)) ≤ 2 := by
  sorry

/-- P0069 page 51, display 5.17 for the E2 sum, the integral with `1` replaced by `s`, an upper
bound for the upward variation. For `s ∈ [99/100, 1]` the integral over the box of the positive
part of the E2 integrand at `s` minus the E2 integrand at one is at most `2 (1 - s)`. A floating
point quadrature gives between `1.43 (1 - s)` and `1.47 (1 - s)`. CONDITIONAL on
`leaf_two_variation_quadrature`. -/
theorem two_density_variation (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {s : ℝ} (hs : 99/100 ≤ s) (hs1 : s ≤ 1) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      max ((if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) -
        (if lowerTwoDiscarded ε a b then ω ((1-a-b)/b)/(a*b^2) else 0)) 0) ≤ 2*(1-s) := by
  have hδ : 0 ≤ 1 - s := by linarith
  have hq := leaf_two_variation_quadrature hε hε8
  have hRm : Measurable (fun p : ℝ × ℝ => (if lowerTwoDiscarded ε p.1 p.2 then
        (if 1 ≤ p.1+3*p.2 then 1/(p.1*p.2*(99/100-p.1-p.2)*(1-p.1-p.2))
          else if 99/100 ≤ p.1+3*p.2 then (107/200)/(p.1*p.2^3) else (7/200)/(p.1*p.2^3))
      else 0)) :=
    Measurable.ite (two_density_region_measurable ε)
      (Measurable.ite (measurableSet_le measurable_const (by fun_prop)) (by fun_prop)
        (Measurable.ite (measurableSet_le measurable_const (by fun_prop)) (by fun_prop)
          (by fun_prop))) measurable_const
  have hm := slope_two_mono
    (fun a b => max ((if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0) -
        (if lowerTwoDiscarded ε a b then ω ((1-a-b)/b)/(a*b^2) else 0)) 0)
    (fun a b => (1-s) * (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0))
    (((two_density_integrand_measurable hω hz ε s).sub
      (two_density_integrand_measurable hω hz ε 1)).max measurable_const)
    (hRm.const_mul (1-s)) (M := 10^4)
    (fun a b => by
      have h1 := two_density_integrand_bound hω hz hε8 s a b
      have h2 := two_density_integrand_bound hω hz hε8 1 a b
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [h1.2, h2.1]) (by norm_num))
    (fun a b => by
      have hb := two_variation_bound hε8 a b
      rw [abs_of_nonneg (mul_nonneg hδ hb.1)]
      nlinarith [hb.1, hb.2])
    (fun a b => two_density_variation_pointwise hω hz hε8 hs hs1 a b)
    (lo := 1/10) (hi := 1/2) (by norm_num)
  simp only [intervalIntegral.integral_const_mul] at hm
  linarith [mul_le_mul_of_nonneg_left hq hδ]

/-- P0069 page 51, display 5.17 for the E2 sum, the integral with `1` replaced by `s`: for
`s ∈ [99/100, 1]` the E2 density is below its value at one by at least `(1/6) (1 - s)`; the
floating point slope of the E2 density at one is about `+1.09`. Lowering `s` removes the
strip `s < a + 2 b ≤ 1` of E2, where `ω` jumps to zero, a loss of at least `(13/6) (1 - s)` by
`two_density_strip_pointwise`, and raises the integrand elsewhere by at most `2 (1 - s)` in the
integral, `two_density_variation`. CONDITIONAL on `leaf_two_variation_quadrature`. -/
theorem two_density_monotone (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ s0 : ℝ, s0 < 1 ∧ ∀ s : ℝ, s0 ≤ s → s ≤ 1 →
      lowerTwoDensityAt ω ε s + (1/6)*(1-s) ≤ lowerTwoDensityAt ω ε 1 := by
  refine ⟨99/100, by norm_num, fun s hs hs1 => ?_⟩
  have hgen := slope_strip_generic
    (fun a b => if lowerTwoDiscarded ε a b then ω ((1-a-b)/b)/(a*b^2) else 0)
    (fun a b => if lowerTwoDiscarded ε a b then ω ((s-a-b)/b)/(a*b^2) else 0)
    (two_density_integrand_measurable hω hz ε 1) (two_density_integrand_measurable hω hz ε s)
    (M := 1000) (fun a b => two_density_integrand_bound hω hz hε8 1 a b)
    (fun a b => two_density_integrand_bound hω hz hε8 s a b)
    (lo := 1/10) (hi := 1/2) (A1 := 1/3) (A2 := 1/2) (c := 26) (w := (1-s)/2)
    (by norm_num) (by norm_num) le_rfl (by linarith) (fun a => (s-a)/2)
    (fun a ha => ⟨by linarith [ha.2], by linarith [ha.1]⟩)
    (fun a ha b hb => two_density_strip_pointwise hω hz hε hε8 hs ha hb)
  have hvar := two_density_variation ω hω hz hε hε8 hs hs1
  unfold lowerTwoDensityAt
  beta_reduce at hgen
  linarith

/-- P0069 page 51, "A computer calculation yields": the certified E2 bound `3799/4000` from the
whole cell grid sum, as in `DecompC165d.lower_two_integral_bound`, with the grid enclosure and
the grid total as hypotheses so that this file need not import the certificate. -/
theorem two_upper_of_grid {I : ℝ} {T : ℕ}
    (hh : I ≤ (T:ℝ)*(37501/409600000:ℝ)^2/10000) (ht : T = 1132433915806) :
    I ≤ 3799/4000 := by
  rw [ht] at hh
  exact hh.trans (by norm_num)

/-- P0069 pages 51 and 52, display 5.17 and the lab normalization: `v0 ≥ 0` and
`V(s) ≥ v0 (1 + 3 (1 - s))` just below `s = 1`, CONDITIONAL on the certified page 51 bound
`h2` for the E2 integral and on the leaves `leaf_two_region_quadrature`
and `leaf_two_variation_quadrature`. With `δ = 1 - s`: `1/s - 1 ≥ δ`, the E2 density drops by at
least `δ / 6`, the E4 density grows by at most `20 δ / 4000`, and `3 v0 - 1 ≤ 1/20`. -/
theorem density_slope_of_two_upper (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (h2 : lowerTwoDeletedIntegral ω ε ≤ 3799/4000) :
    0 ≤ lowerV0 ω ε ∧ ∃ s0 : ℝ, s0 < 1 ∧ ∀ s : ℝ, s0 ≤ s → s ≤ 1 →
      lowerV0 ω ε * (1 + 3 * (1 - s)) ≤ lowerDensityAt ω ε s := by
  have h4 := lower_four_discard_small hω hz hε.le hε8
  have hlow := two_density_lower ω hω hz hε hε8
  obtain ⟨s0, hs0, hmono⟩ := two_density_monotone ω hω hz hε hε8
  have hone := lowerDensityAt_one ω ε
  have h21 : lowerTwoDensityAt ω ε 1 = lowerTwoDeletedIntegral ω ε := rfl
  have h41 : lowerFourDensityAt ω ε 1 = lowerFourDeletedIntegral ω ε := by
    unfold lowerDensityAt lowerV0 at hone
    rw [h21, div_one] at hone
    linarith
  refine ⟨by unfold lowerV0; linarith, max s0 (99/100), max_lt hs0 (by norm_num), ?_⟩
  intro s hs hs1
  have hs99 : (99/100:ℝ) ≤ s := (le_max_right _ _).trans hs
  have hm := hmono s ((le_max_left _ _).trans hs) hs1
  have hd := four_density_drop hω hz hε hε8 hs99 hs1
  rw [h41] at hd
  rw [h21] at hm
  have hs0' : 0 < s := by linarith
  have hinv : 2 - s ≤ 1 / s := by
    rw [le_div_iff₀ hs0']
    nlinarith [sq_nonneg (1 - s)]
  unfold lowerDensityAt lowerV0
  have hδ : 0 ≤ 1 - s := by linarith
  nlinarith [mul_nonneg hδ (by linarith : (0:ℝ) ≤ lowerTwoDeletedIntegral ω ε - 13/20),
    mul_nonneg hδ (by linarith : (0:ℝ) ≤ 1/4000 - lowerFourDeletedIntegral ω ε)]

end LeanLab.BHP1997.LowerShortC165
