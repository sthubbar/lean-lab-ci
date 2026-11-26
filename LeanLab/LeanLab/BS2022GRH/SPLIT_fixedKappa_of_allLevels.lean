/-
Split of the OPEN target `fixedKappa_of_allLevels` of SieveAllLevels1611 into four leaves, with an
assembly that has the target's statement verbatim and uses no sorry.

The target is the lab's own reduction, written out in the doc comment of the target, U-1611: the
fixed level linear sieve with κ weights in the remainder follows from the all levels sieve of
Bordignon, Johnston, Starichkova, Theorem 2.1 and Lemma 2.7, as quoted for P0021 p. 1218. Its hand
proof has a construction part, steps 1 to 7, and a limit part, step 8. With z' = exp(M C),
C = (1 + εF) log z and D' = (D(1 - δ))^M, the level of the lifted system is
log D' / log z' = log (D(1 - δ)) / log z / (1 + εF) for every M, so the construction gives the bound
at exactly this level for each δ, and only the limit δ → 0 is left for step 8.

Leaf 1, HARD: steps 1 to 7 plus one application of the all levels sieve, at a fixed δ.
Leaf 2, MEDIUM: step 8 for the upper bound, continuity of 2e^γ/s + c h(s) at s > 0.
Leaf 3, MEDIUM: step 8 for the lower bound, continuity of 2e^γ log(s - 1)/s - c h(s) at s > 1.
Leaf 4, MEDIUM: the level log (D(1 - δ)) / log z / (1 + εF) tends to s* as δ → 0+.

This file adds no definition, changes no existing file, and leaves the sealed statement untouched.
The assembly declares neither the target nor any leaf as a hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SieveAllLevels1611

namespace LeanLab.BS2022GRH.SieveAllLevels1611
open Real Finset Classical Filter Topology
open LeanLab.BS2022GRH LeanLab.BS2022GRH.ChenThresholdGRH

private lemma continuous_inner_hS : Continuous
    (fun s : ℝ => if s ≤ 3 then exp (-s) else 3 / s * exp (-s)) := by
  apply Continuous.if_le
  · fun_prop
  · intro s hs
    have hs0 : s ≠ 0 := by linarith
    fun_prop
  · exact continuous_id
  · exact continuous_const
  · intro s hs
    have h3 : s = 3 := hs
    subst s
    simp

private lemma continuous_hS : Continuous hS := by
  change Continuous (fun s : ℝ =>
    if s ≤ 2 then exp (-2) else if s ≤ 3 then exp (-s) else 3 / s * exp (-s))
  apply Continuous.if_le
  · exact continuous_const
  · exact continuous_inner_hS.continuousOn
  · exact continuous_id
  · exact continuous_const
  · intro s hs
    have h2 : s = 2 := hs
    subst s
    simp

/-- LEAF: steps 1 to 7 of the hand proof of `fixedKappa_of_allLevels`, then one use of
`LinearSieveAllLevels` at z' = exp(M (1 + εF) log z), D' = (D(1 - δ))^M, M large; the new level is
sδ for every M. HARD: needs Mertens on all primes of a range, not in Mathlib. Strictly easier than
the target: level sδ < s*, no limit. Non-vacuity: see `fixedPremise_of_lemma7`. -/
theorem lifted_bound_of_allLevels {εF ε C₁ C₂ : ℝ} (h : LinearSieveAllLevels ε C₁ C₂) :
  ∀ (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ),
    (∀ n, 0 ≤ a n) → (∀ n, n ∉ supp → a n = 0) → (∀ p ∈ P, p.Prime) → (↑Q ⊆ P) →
    (∀ q ∈ Q, (q : ℝ) < z) → (∀ p ∈ P, 0 < g p ∧ g p < 1) →
    0 < εF → 0 < ε → ε < 1 / 63 → 2 ≤ z →
    FixedPremise P Q g εF z →
    let Pz := (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ (p : ℝ) < z)
    let S := ∑ n ∈ supp.filter (fun n => ∀ p ∈ Pz, ¬ p ∣ n), a n
    let X := ∑ n ∈ supp, a n * ∏ p ∈ Pz, (1 - g p)
    let r := fun d : ℕ => (∑ n ∈ supp.filter (fun n => d ∣ n), a n)
      - ∑ n ∈ supp, a n * ∏ p ∈ d.primeFactors, g p
    let Rκ := ∑ T ∈ Pz.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q, p : ℕ) * D),
      kappaT Q g T * |r (∏ p ∈ T, p)|
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    let sδ := log (D * (1 - δ)) / log z / (1 + εF)
    (z ^ (1 + εF) < D * (1 - δ) → log D / log z / (1 + εF) ≤ 3 →
      S ≤ (2 * exp eulerMascheroniConstant / sδ + ε * C₁ * exp 2 * hS sδ) * X + Rκ) ∧
    (z ^ (2 * (1 + εF)) < D * (1 - δ) → log D / log z / (1 + εF) ≤ 4 →
      (2 * exp eulerMascheroniConstant * log (sδ - 1) / sδ - ε * C₂ * exp 2 * hS sδ) * X - Rκ
        ≤ S) := by
  sorry

/-- LEAF: step 8, upper half. F(s) = 2e^γ/s and h(s) are continuous at s₀ > 0, `hS` agrees at the
break points 2 and 3, so a bound S ≤ (F(f δ) + c h(f δ)) X + R holding for all small δ > 0 passes to
the limit s₀ of f δ. MEDIUM: continuity of a piecewise function and closedness of ≤. Strictly
easier than the target: pure real analysis, no sieve. Non-vacuity: f constant equal to s₀ = 1 with
S = 0, X = R = 0 satisfies the hypothesis. -/
theorem upper_limit (S X R c s₀ : ℝ) (hs₀ : 0 < s₀) (f : ℝ → ℝ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 s₀))
    (hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      S ≤ (2 * exp eulerMascheroniConstant / f δ + c * hS (f δ)) * X + R) :
    S ≤ (2 * exp eulerMascheroniConstant / s₀ + c * hS s₀) * X + R := by
  have hF : ContinuousAt
      (fun s : ℝ => 2 * exp eulerMascheroniConstant / s + c * hS s) s₀ := by
    exact ((continuousAt_const.div continuousAt_id hs₀.ne').add
      ((continuous_hS.continuousAt).const_mul c))
  have hR : ContinuousAt
      (fun s : ℝ => (2 * exp eulerMascheroniConstant / s + c * hS s) * X + R) s₀ := by
    exact (hF.mul_const X).add continuousAt_const
  have hlim : Tendsto
      (fun δ : ℝ => (2 * exp eulerMascheroniConstant / f δ + c * hS (f δ)) * X + R)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((2 * exp eulerMascheroniConstant / s₀ + c * hS s₀) * X + R)) :=
    hR.tendsto.comp hf
  exact Filter.ge_of_tendsto hlim hev

/-- LEAF: step 8, lower half. f(s) = 2e^γ log(s - 1)/s and h(s) are continuous at s₀ > 1, so a
bound holding for all small δ > 0 passes to the limit s₀ of f δ. MEDIUM, as `upper_limit`. Strictly
easier than the target: pure real analysis. Non-vacuity: f constant equal to s₀ = 3 with
S = X = R = 0. -/
theorem lower_limit (S X R c s₀ : ℝ) (hs₀ : 1 < s₀) (f : ℝ → ℝ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 s₀))
    (hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (2 * exp eulerMascheroniConstant * log (f δ - 1) / f δ - c * hS (f δ)) * X - R ≤ S) :
    (2 * exp eulerMascheroniConstant * log (s₀ - 1) / s₀ - c * hS s₀) * X - R ≤ S := by
  have hlog : ContinuousAt (fun s : ℝ => log (s - 1)) s₀ :=
    (Real.continuousAt_log (by linarith : s₀ - 1 ≠ 0)).comp
      (continuousAt_id.sub continuousAt_const)
  have hF : ContinuousAt
      (fun s : ℝ => 2 * exp eulerMascheroniConstant * log (s - 1) / s - c * hS s) s₀ := by
    exact (((continuousAt_const.mul hlog).div continuousAt_id hs₀.ne').sub
      ((continuous_hS.continuousAt).const_mul c))
  have hR : ContinuousAt
      (fun s : ℝ => (2 * exp eulerMascheroniConstant * log (s - 1) / s - c * hS s) * X - R) s₀ := by
    exact (hF.mul_const X).sub continuousAt_const
  have hlim : Tendsto
      (fun δ : ℝ => (2 * exp eulerMascheroniConstant * log (f δ - 1) / f δ - c * hS (f δ)) * X - R)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((2 * exp eulerMascheroniConstant * log (s₀ - 1) / s₀ - c * hS s₀) * X - R)) :=
    hR.tendsto.comp hf
  exact Filter.le_of_tendsto hlim hev

/-- LEAF: step 8, the level. For D > 0 and z ≥ 2 the level log (D(1 - δ)) / log z / (1 + εF) of
the lifted system tends to s* = log D / log z / (1 + εF) as δ → 0+. MEDIUM: continuity of log at
D > 0. Strictly easier than the target. Non-vacuity: z = 2, D = 1, εF = 1. -/
theorem level_tendsto (z D εF : ℝ) (hD : 0 < D) :
    Tendsto (fun δ => log (D * (1 - δ)) / log z / (1 + εF)) (𝓝[>] 0)
      (𝓝 (log D / log z / (1 + εF))) := by
  have hc : Tendsto (fun δ : ℝ => D * (1 - δ)) (𝓝[>] (0 : ℝ)) (𝓝 D) := by
    convert ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds using 1 <;> simp
  have hl : Tendsto (fun δ : ℝ => log (D * (1 - δ))) (𝓝[>] (0 : ℝ)) (𝓝 (log D)) :=
    hc.log hD.ne'
  exact (hl.div_const (log z)).div_const (1 + εF)

/-- The eventual conditions on δ, PROVED: for w < D, small δ > 0 has δ < 1 and w < D(1 - δ). -/
theorem eventually_small (w D : ℝ) (hw : w < D) (hD : 0 < D) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < 1 ∧ w < D * (1 - δ) := by
  have hc : Tendsto (fun δ : ℝ => D * (1 - δ)) (𝓝[>] 0) (𝓝 (D * (1 - 0))) :=
    ((continuous_const.mul (continuous_const.sub continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  rw [sub_zero, mul_one] at hc
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), w < D * (1 - δ) := hc.eventually (lt_mem_nhds hw)
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have h3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h1, h2, h3] with δ a b c using ⟨b, c, a⟩

/-- **Assembly**, CONDITIONAL ON the four leaves: the target statement verbatim. -/
theorem fixedKappa_of_allLevels_split {εF ε C₁ C₂ : ℝ} (h : LinearSieveAllLevels ε C₁ C₂) :
    LinearSieveFixedKappa εF ε C₁ C₂ := by
  intro supp a P Q g z D ha hs hP hQ hQz hg hεF hε hε63 hz hfix
  have L := lifted_bound_of_allLevels (εF := εF) h supp a P Q g z D ha hs hP hQ hQz hg hεF hε
    hε63 hz hfix
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < log z := log_pos (by linarith : 1 < z)
  have h1εF : 0 < 1 + εF := by linarith
  have hlim := level_tendsto z D εF
  intro Pz S X r Rκ sS
  refine ⟨fun hD hs3 => ?_, fun hD hs4 => ?_⟩
  · have hD0 : 0 < D := lt_trans (rpow_pos_of_pos hzpos _) hD
    have hsS : 0 < sS := by
      have hzD : log (z ^ (1 + εF)) < log D := log_lt_log (rpow_pos_of_pos hzpos _) hD
      rw [log_rpow hzpos] at hzD
      have : 0 < log D := lt_trans (by positivity) hzD
      positivity
    apply upper_limit S X Rκ (ε * C₁ * exp 2) sS hsS _ (hlim hD0)
    filter_upwards [eventually_small _ D hD hD0] with δ ⟨h0, h1, h2⟩
    exact (L δ h0 h1).1 h2 hs3
  · have hz2 : 0 < z ^ (2 * (1 + εF)) := rpow_pos_of_pos hzpos _
    have hD0 : 0 < D := lt_trans hz2 hD
    have hsS : 1 < sS := by
      have hzD : log (z ^ (2 * (1 + εF))) < log D := log_lt_log hz2 hD
      rw [log_rpow hzpos] at hzD
      have h2 : 2 * (1 + εF) < log D / log z := by rw [lt_div_iff₀ hlogz]; linarith
      have h3 : 2 < log D / log z / (1 + εF) := by rw [lt_div_iff₀ h1εF]; linarith
      show 1 < log D / log z / (1 + εF)
      linarith
    apply lower_limit S X Rκ (ε * C₂ * exp 2) sS hsS _ (hlim hD0)
    filter_upwards [eventually_small _ D hD hD0] with δ ⟨h0, h1, h2⟩
    exact (L δ h0 h1).2 h2 hs4

end LeanLab.BS2022GRH.SieveAllLevels1611

#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.lifted_bound_of_allLevels
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.upper_limit
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.lower_limit
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.level_tendsto
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.eventually_small
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.fixedKappa_of_allLevels_split
