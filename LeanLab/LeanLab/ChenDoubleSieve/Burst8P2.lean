import LeanLab.ChenDoubleSieve.Burst4Split
import LeanLab.ChenDoubleSieve.Xi2Signs
import LeanLab.ChenDoubleSieve.NormalizerPositive

/-!
# Burst 8, pass 2: further splits of the Wu 2004 Theorem 1 leaves

P0036 J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
Acta Arith. 114 (2004) 215 to 273, arXiv 0705.1652. Page numbers are those of the arXiv
version.

AI wrote this Lean code. Binary Goldbach is OPEN; Theorem 1 is an upper bound for `D(N)`.

This file adds new declarations only. Each leaf of `Burst4Split` handled here is reproved
from finer pieces that follow Wu's own proof; the cited analytic pieces stay `sorry`
with page and display, and the glue between them is proved.
-/

set_option maxHeartbeats 1000000
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Burst8P2
open Wu04Functional
open Wu04Integral (sigma0)

/-! ### Part A. Integrability of the kernels, displays 3.21, 3.22, 7.1 and 7.2 -/

/-- A summand `1_{[a,b]}(t) / D(t) · log G(t)` of Wu's kernels on page 14 is integrable on
`[1, 3]` when `D` and `G` are continuous and nonzero on the support. -/
theorem ind_log_integrable {a b : ℝ} {D G : ℝ → ℝ}
    (hD : ContinuousOn D (Icc a b ∩ Icc 1 3)) (hD0 : ∀ t ∈ Icc a b ∩ Icc 1 3, D t ≠ 0)
    (hG : ContinuousOn G (Icc a b ∩ Icc 1 3)) (hG0 : ∀ t ∈ Icc a b ∩ Icc 1 3, G t ≠ 0) :
    IntervalIntegrable (fun t => ind a b t / D t * log (G t)) volume 1 3 := by
  have he : (fun t => ind a b t / D t * log (G t)) =
      (Icc a b).indicator (fun t => log (G t) / D t) := by
    funext t
    by_cases h : a ≤ t ∧ t ≤ b
    · rw [ind, if_pos h, indicator_of_mem (show t ∈ Icc a b from h)]; ring
    · rw [ind, if_neg h, indicator_of_notMem (show t ∉ Icc a b from h)]; ring
  rw [he, intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3),
    IntegrableOn, integrable_indicator_iff measurableSet_Icc, IntegrableOn,
    Measure.restrict_restrict measurableSet_Icc]
  exact ((hG.log hG0).div hD hD0).integrableOn_compact (isCompact_Icc.inter isCompact_Icc)

/-- The `σ₀` summand of the kernels on page 14 is integrable on `[1, 3]`, since `σ₀` is
increasing there, `Wu04Integral.sigma0_mono`. -/
theorem sigma_term_integrable (c L : ℝ) (hc : 0 < c) :
    IntervalIntegrable (fun t => Wu04Integral.sigma0 t / (c * t) * L) volume 1 3 := by
  have hm : IntervalIntegrable Wu04Integral.sigma0 volume 1 3 := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact Wu04Integral.sigma0_mono.mono (fun t ht => mem_Ici.2 ht.1)
  have hg : ContinuousOn (fun t : ℝ => L / (c * t)) (uIcc 1 3) := by
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    show c * t ≠ 0
    exact (mul_pos hc (show (0 : ℝ) < t by linarith [ht.1])).ne'
  have he : (fun t => Wu04Integral.sigma0 t / (c * t) * L) =
      fun t => Wu04Integral.sigma0 t * (L / (c * t)) := by
    funext t; ring
  rw [he]
  exact hm.mul_continuousOn hg

/-- `Ξ₁(·; s, s')` of display 3.21, page 14, is integrable on `[1, 3]` on the full parameter
range of Proposition 3. -/
theorem Xi1_integrable {s sp : ℝ} (hp : Admissible3 s sp) :
    IntervalIntegrable (Xi1 s sp) volume 1 3 := by
  obtain ⟨hs2, hs3, hsp3, hsp5, hss⟩ := hp
  have h1 := sigma_term_integrable 2 (log (16 / ((s - 1) * (sp - 1)))) (by norm_num)
  have h2 : IntervalIntegrable (fun t => ind (sp - 2) 3 t / (2 * t) *
      log ((t + 1) ^ 2 / ((s - 1) * (sp - 1)))) volume 1 3 := by
    apply ind_log_integrable
    · fun_prop
    · intro t ht; exact (show (0 : ℝ) < 2 * t by linarith [ht.2.1]).ne'
    · fun_prop
    · intro t ht
      have h0 : (0 : ℝ) < (s - 1) * (sp - 1) := mul_pos (by linarith) (by linarith)
      exact (div_pos (by nlinarith [ht.2.1]) h0).ne'
  have h3 : IntervalIntegrable (fun t => ind (sp - sp / s - 1) (sp - 2) t / (2 * t) *
      log ((t + 1) / ((s - 1) * (sp - 1 - t)))) volume 1 3 := by
    apply ind_log_integrable
    · fun_prop
    · intro t ht; exact (show (0 : ℝ) < 2 * t by linarith [ht.2.1]).ne'
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      exact (mul_pos (by linarith) (by linarith [ht.1.2])).ne'
    · intro t ht
      have h0 : (0 : ℝ) < (s - 1) * (sp - 1 - t) := mul_pos (by linarith) (by linarith [ht.1.2])
      exact (div_pos (by linarith [ht.2.1]) h0).ne'
  exact (h1.add h2).add h3

/-- The sign conditions of `Wu04Functional.tableXi2_log_signs`, for a general parameter
vector: on each support interval of display 3.22 the denominator of the logarithm is positive
and at most its numerator. -/
def Xi2Signs (p : Params) : Prop :=
  ∀ t ∈ Icc (1 : ℝ) 3,
    let a := alpha p
    let P := (p.s-1)*(p.sp-1)*(p.k1-1)*(p.k2-1)*(p.k3-1)
    ((a 1 ≤ t ∧ t ≤ 3) → 0 < P ∧ P ≤ (t+1)^5) ∧
    ((a 8 ≤ t ∧ t ≤ a 0) → 0 < (p.k2-1)*(p.k1-1-t) ∧ (p.k2-1)*(p.k1-1-t) ≤ t+1) ∧
    ((a 4 ≤ t ∧ t ≤ a 1) → 0 < (p.k3-1)*(p.sp-1-t) ∧ (p.k3-1)*(p.sp-1-t) ≤ t+1) ∧
    ((a 2 ≤ t ∧ t ≤ a 1) → 0 < (p.s-1)*(p.sp-1-t) ∧ (p.s-1)*(p.sp-1-t) ≤ t+1) ∧
    ((a 0 ≤ t ∧ t ≤ a 1) → 0 < (p.k1-1)*(p.k2-1) ∧ (p.k1-1)*(p.k2-1) ≤ (t+1)^2) ∧
    ((a 6 ≤ t ∧ t ≤ a 4) →
      0 < (p.k1*p.sp-p.sp-p.k1*t)*(p.k3*p.sp-p.sp-p.k3*t) ∧
      (p.k1*p.sp-p.sp-p.k1*t)*(p.k3*p.sp-p.sp-p.k3*t) ≤ p.sp^2) ∧
    ((a 4 ≤ t ∧ t ≤ a 7) → 0 < p.k1*p.sp-p.sp-p.k1*t ∧
      p.k1*p.sp-p.sp-p.k1*t ≤ p.sp*(p.sp-1-t)) ∧
    ((a 5 ≤ t ∧ t ≤ a 7) → 0 < p.k2*p.sp-p.sp-p.k2*t ∧
      p.k2*p.sp-p.sp-p.k2*t ≤ p.sp) ∧
    ((a 7 ≤ t ∧ t ≤ a 1) → 0 < (1 : ℝ) ∧ 1 ≤ p.sp-1-t)

/-- The four Table 1 rows satisfy `Xi2Signs`, by the PROVED `tableXi2_log_signs`. -/
theorem tableParams_Xi2Signs (i : Fin 4) : Xi2Signs (tableParams i) :=
  fun _ ht => tableXi2_log_signs i ht

/-- `Ξ₂(·; s, s', κ₁, κ₂, κ₃)` of display 3.22, page 15, is integrable on `[1, 3]` whenever
`3 < s'` and the logarithms have positive arguments on their supports. -/
theorem Xi2_integrable {p : Params} (hsp : 3 < p.sp) (hS : Xi2Signs p) :
    IntervalIntegrable (Xi2 p) volume 1 3 := by
  have hq : ∀ t ∈ Icc (1 : ℝ) 3, 5 * t * (1 - t / p.sp) ≠ 0 := by
    intro t ht
    have hsp0 : 0 < p.sp := by linarith
    have : t / p.sp < 1 := (div_lt_one hsp0).2 (by linarith [ht.2])
    exact (mul_pos (by linarith [ht.1]) (by linarith)).ne'
  have h5t : ∀ t ∈ Icc (1 : ℝ) 3, 5 * t ≠ 0 := fun t ht => by
    exact (show (0 : ℝ) < 5 * t by linarith [ht.1]).ne'
  have hspc : ContinuousOn (fun t : ℝ => 5 * t * (1 - t / p.sp)) univ := by fun_prop
  have h1 := sigma_term_integrable 5
    (log (1024 / ((p.s - 1) * (p.sp - 1) * (p.k1 - 1) * (p.k2 - 1) * (p.k3 - 1)))) (by norm_num)
  have h2 : IntervalIntegrable (fun t => ind (alpha p 1) 3 t / (5 * t) *
      log ((t + 1) ^ 5 / ((p.s - 1) * (p.sp - 1) * (p.k1 - 1) * (p.k2 - 1) * (p.k3 - 1))))
      volume 1 3 := by
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2) (by fun_prop)
    intro t ht
    have := ((hS t ht.2).1 ht.1).1
    exact (div_pos (pow_pos (by linarith [ht.2.1]) 5) this).ne'
  have h3 : IntervalIntegrable (fun t => ind (alpha p 8) (alpha p 0) t / (5 * t) *
      log ((t + 1) / ((p.k2 - 1) * (p.k1 - 1 - t)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 8) (alpha p 0) ∩ Icc 1 3) =>
      ((hS t ht.2).2.1 ht.1)
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) (hd t ht).1).ne'
  have h4 : IntervalIntegrable (fun t => ind (alpha p 4) (alpha p 1) t / (5 * t) *
      log ((t + 1) / ((p.k3 - 1) * (p.sp - 1 - t)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 4) (alpha p 1) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.1 ht.1)
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) (hd t ht).1).ne'
  have h5 : IntervalIntegrable (fun t => ind (alpha p 2) (alpha p 1) t / (5 * t) *
      log ((t + 1) / ((p.s - 1) * (p.sp - 1 - t)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 2) (alpha p 1) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.1 ht.1)
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) (hd t ht).1).ne'
  have h6 : IntervalIntegrable (fun t => ind (alpha p 0) (alpha p 1) t / (5 * t) *
      log ((t + 1) ^ 2 / ((p.k1 - 1) * (p.k2 - 1)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 0) (alpha p 1) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.1 ht.1)
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2) (by fun_prop)
    intro t ht
    exact (div_pos (by nlinarith [ht.2.1]) (hd t ht).1).ne'
  have h7 : IntervalIntegrable (fun t => ind (alpha p 6) (alpha p 4) t /
      (5 * t * (1 - t / p.sp)) * log (p.sp ^ 2 /
      ((p.k1 * p.sp - p.sp - p.k1 * t) * (p.k3 * p.sp - p.sp - p.k3 * t)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 6) (alpha p 4) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.2.1 ht.1)
    apply ind_log_integrable (hspc.mono (subset_univ _)) (fun t ht => hq t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by nlinarith) (hd t ht).1).ne'
  have h8 : IntervalIntegrable (fun t => ind (alpha p 4) (alpha p 7) t /
      (5 * t * (1 - t / p.sp)) * log (p.sp * (p.sp - 1 - t) /
      (p.k1 * p.sp - p.sp - p.k1 * t))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 4) (alpha p 7) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.2.2.1 ht.1)
    apply ind_log_integrable (hspc.mono (subset_univ _)) (fun t ht => hq t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos ((hd t ht).1.trans_le (hd t ht).2) (hd t ht).1).ne'
  have h9 : IntervalIntegrable (fun t => ind (alpha p 5) (alpha p 7) t /
      (5 * t * (1 - t / p.sp)) * log (p.sp / (p.k2 * p.sp - p.sp - p.k2 * t))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 5) (alpha p 7) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.2.2.2.1 ht.1)
    apply ind_log_integrable (hspc.mono (subset_univ _)) (fun t ht => hq t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by linarith) (hd t ht).1).ne'
  have h10 : IntervalIntegrable (fun t => ind (alpha p 7) (alpha p 1) t /
      (5 * t * (1 - t / p.sp)) * log (p.sp - 1 - t)) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 7) (alpha p 1) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.2.2.2.2 ht.1)
    apply ind_log_integrable (hspc.mono (subset_univ _)) (fun t ht => hq t ht.2) (by fun_prop)
    intro t ht
    exact (show (0 : ℝ) < p.sp - 1 - t by linarith [(hd t ht).2]).ne'
  exact (((((((((h1.add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10)

/-- **Leaf `table_kernel_integrable` PROVED.** Wu 2004 displays 7.1 and 7.2, page 30: each of
the nine Table 1 kernels is integrable on `[1, 3]`. Same statement as
`Burst4Split.table_kernel_integrable`. -/
theorem table_kernel_integrable :
    ∀ i : Fin 9, IntervalIntegrable (Wu04Table.tableKernel i) volume 1 3 := by
  intro i
  unfold Wu04Table.tableKernel
  split_ifs with hi
  · apply Xi2_integrable _ (tableParams_Xi2Signs ⟨i.val, hi⟩)
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases this with h | h | h | h <;> simp [h, tableParams]  <;> norm_num
  · let j : Fin 5 := ⟨i.val - 4, by omega⟩
    have hp := tableSp_admissible j
    have he : (⟨j.val + 5, by omega⟩ : Fin 10) = ⟨i.val + 1, by omega⟩ := by
      ext; dsimp [j]; omega
    rw [he] at hp
    exact Xi1_integrable hp


/-- The support indicator `1_{[a,b]}(t)/D(t)` is integrable on `[1, 3]`. -/
theorem ind_integrable {a b : ℝ} {D : ℝ → ℝ}
    (hD : ContinuousOn D (Icc a b ∩ Icc 1 3)) (hD0 : ∀ t ∈ Icc a b ∩ Icc 1 3, D t ≠ 0) :
    IntervalIntegrable (fun t => ind a b t / D t) volume 1 3 := by
  have he : (fun t => ind a b t / D t) = (Icc a b).indicator (fun t => 1 / D t) := by
    funext t
    by_cases h : a ≤ t ∧ t ≤ b
    · rw [ind, if_pos h, indicator_of_mem (show t ∈ Icc a b from h)]
    · rw [ind, if_neg h, indicator_of_notMem (show t ∉ Icc a b from h)]; simp
  rw [he, intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3),
    IntegrableOn, integrable_indicator_iff measurableSet_Icc, IntegrableOn,
    Measure.restrict_restrict measurableSet_Icc]
  exact (continuousOn_const.div hD hD0).integrableOn_compact (isCompact_Icc.inter isCompact_Icc)

/-- `σ₀(t)/t · L` is integrable on `[1, 3]`. -/
theorem sigma_div_integrable (L : ℝ) :
    IntervalIntegrable (fun t => sigma0 t / t * L) volume 1 3 := by
  have he : (fun t => sigma0 t / t * L) = (fun t => sigma0 t / (1 * t) * L) := by
    funext t; rw [one_mul]
  rw [he]
  exact sigma_term_integrable 1 L one_pos

/-- The kernel of display 6.2 is integrable on `[1, 3]`. -/
theorem kernel62_integrable {sp : ℝ} (hsp : 3 ≤ sp) :
    IntervalIntegrable (fun t => sigma0 t / t * log (4 / (sp - 1)) +
      ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1))) volume 1 3 := by
  refine (sigma_div_integrable _).add ?_
  apply ind_log_integrable
  · fun_prop
  · intro t ht; exact (show (0 : ℝ) < t by linarith [ht.2.1]).ne'
  · fun_prop
  · intro t ht
    exact (div_pos (by linarith [ht.2.1]) (by linarith)).ne'

/-- The first kernel of display 6.3 is integrable on `[1, 3]`. -/
theorem kernel63a_integrable (x : ℝ) :
    IntervalIntegrable (fun t => (sigma0 t + ind x 3 t) / t) volume 1 3 := by
  have he : (fun t => (sigma0 t + ind x 3 t) / t) =
      (fun t => sigma0 t / t * 1 + ind x 3 t / t) := by
    funext t; ring
  rw [he]
  refine (sigma_div_integrable 1).add ?_
  apply ind_integrable
  · fun_prop
  · intro t ht; exact (show (0 : ℝ) < t by linarith [ht.2.1]).ne'

/-- The second kernel of display 6.3, at `a = 1 − 1/s`, `b = 1 − 1/s'`, `c = s'`, in simplified
form, is integrable on `[1, 3]`. -/
theorem kernel63b_integrable {s sp : ℝ} (hs : 2 ≤ s) :
    IntervalIntegrable (fun t => ind (sp - sp / s - 1) (sp - 2) t / t *
      log ((t + 1) / ((s - 1) * (sp - 1 - t)))) volume 1 3 := by
  apply ind_log_integrable
  · fun_prop
  · intro t ht; exact (show (0 : ℝ) < t by linarith [ht.2.1]).ne'
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact (mul_pos (by linarith) (by linarith [ht.1.2])).ne'
  · intro t ht
    have h0 : (0 : ℝ) < (s - 1) * (sp - 1 - t) := mul_pos (by linarith) (by linarith [ht.1.2])
    exact (div_pos (by linarith [ht.2.1]) h0).ne'

/-! ### Part B. Proposition 1, page 10 -/

/-- SUB-LEAF of `proposition1`, upper half. Wu 2004 Proposition 1, page 10, proof on pages 10
and 11: Lemma 2.2 with display 3.10 gives display 3.11 and then 3.12, and the remainder
estimate 3.13 with 3.7 gives `Φ(N, σ, s) ≤ {A(s) + O_{δ,k}(ε)} Θ(N, σ)` for `N ≥ N₀`. Since
`ε` is arbitrary this says: for every `ε > 0`, `c = −ε` is a candidate in the definition of
`H_{k,N₀}(s)` for some `N₀`. Cited, it rests on the linear sieve Lemma 2.2 and the mean value
theorem Lemma 2.3. -/
theorem prop1_upper_eps {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ k : ℕ, 1 ≤ k → ∀ s ∈ Icc (1 : ℝ) 10,
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, Wu04.UpperCandidate F δ k N₀ s (-ε) := by
  sorry

/-- SUB-LEAF of `proposition1`, lower half. Wu 2004 Proposition 1, page 10, the second
inequality, "treated similarly" on page 11: `Φ(N, σ, s) ≥ {a(s) − O_{δ,k}(ε)} Θ(N, σ)` for
`N ≥ N₀`, that is `c = −ε` is a candidate in the definition of `h_{k,N₀}(s)`. -/
theorem prop1_lower_eps {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ k : ℕ, 1 ≤ k → ∀ s ∈ Icc (1 : ℝ) 10,
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, Wu04.LowerCandidate f δ k N₀ s (-ε) := by
  sorry

/-- An extended real that is at least `−ε` for every `ε > 0` is nonnegative: the step "first
making `N₀ → ∞` and then `ε → 0`" at the end of the proof of Proposition 1, page 11. -/
theorem ereal_nonneg_of_forall {x : EReal}
    (h : ∀ ε : ℝ, 0 < ε → ((-ε : ℝ) : EReal) ≤ x) : 0 ≤ x := by
  induction x using EReal.rec with
  | bot => exact absurd (le_bot_iff.mp (h 1 one_pos)) (EReal.coe_ne_bot _)
  | coe r =>
    have hr : ∀ ε : ℝ, 0 < ε → -ε ≤ r := fun ε hε => by exact_mod_cast h ε hε
    have : 0 ≤ r := by
      by_contra hneg
      have hneg' : r < 0 := not_le.mp hneg
      have := hr (-r / 2) (by linarith)
      linarith
    exact_mod_cast this
  | top => exact le_top

/-- Proposition 1 for `H_k`, page 10, from the sub-leaf `prop1_upper_eps`. -/
theorem Hk_nonneg {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ k : ℕ, 1 ≤ k → ∀ s ∈ Icc (1 : ℝ) 10,
      0 ≤ Wu04.Hk F δ k s := by
  obtain ⟨δ₀, hδ₀, hU⟩ := prop1_upper_eps hF
  refine ⟨δ₀, hδ₀, fun δ hδ hδ' k hk s hs => ereal_nonneg_of_forall fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hU δ hδ hδ' k hk s hs ε hε
  exact (le_sSup ⟨-ε, hN₀, rfl⟩ : ((-ε : ℝ) : EReal) ≤ Wu04.Hkn F δ k N₀ s).trans
    (le_iSup (fun N₀ => Wu04.Hkn F δ k N₀ s) N₀)

/-- Proposition 1 for `h_k`, page 10, from the sub-leaf `prop1_lower_eps`. -/
theorem hk_nonneg {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ k : ℕ, 1 ≤ k → ∀ s ∈ Icc (1 : ℝ) 10,
      0 ≤ Wu04.hk f δ k s := by
  obtain ⟨δ₀, hδ₀, hL⟩ := prop1_lower_eps hF
  refine ⟨δ₀, hδ₀, fun δ hδ hδ' k hk s hs => ereal_nonneg_of_forall fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hL δ hδ hδ' k hk s hs ε hε
  exact (le_sSup ⟨-ε, hN₀, rfl⟩ : ((-ε : ℝ) : EReal) ≤ Wu04.hkn f δ k N₀ s).trans
    (le_iSup (fun N₀ => Wu04.hkn f δ k N₀ s) N₀)

/-- **Leaf `proposition1` from its split.** Wu 2004 Proposition 1, page 10, passed to the limit
`k → ∞` that defines `H` and `h` on page 10. Same statement as `Burst4Split.proposition1`.
CONDITIONAL ON `prop1_upper_eps` and `prop1_lower_eps`. -/
theorem proposition1 {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ s ∈ Icc (1 : ℝ) 10, 0 ≤ H s ∧ 0 ≤ h s := by
  obtain ⟨d1, hd1, hU⟩ := Hk_nonneg hF
  obtain ⟨d2, hd2, hL⟩ := hk_nonneg hF
  refine ⟨min d1 d2, lt_min hd1 hd2, fun δ hδ hδ' H h hR s hs => ?_⟩
  have h1 : δ < d1 := hδ'.trans_le (min_le_left _ _)
  have h2 : δ < d2 := hδ'.trans_le (min_le_right _ _)
  obtain ⟨eH, eh⟩ := hR s hs
  constructor
  · have : (0 : EReal) ≤ (H s : EReal) := by
      rw [eH]
      exact le_iInf fun k => hU δ hδ h1 (k + 1) (by omega) s hs
    exact_mod_cast this
  · have : (0 : EReal) ≤ (h s : EReal) := by
      rw [eh]
      exact le_iInf fun k => hL δ hδ h2 (k + 1) (by omega) s hs
    exact_mod_cast this

/-! ### Part C. Corollary 1, page 13 -/

/-- `A(s) = 1` for `1 ≤ s ≤ 3`, used in the proof of Corollary 1, page 13. For `s ≤ 2` this is
display 2.6; on `(2, 3]` the equation `(uF(u))' = f(u − 1)` with `f = 0` on `(0, 2]` keeps
`uF(u)` constant, by the mean value theorem. -/
theorem normalized_eq_one {F f : ℝ → ℝ} (hF : IsLinearSieve F f) {s : ℝ}
    (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : Wu04.normalized F s = 1 := by
  obtain ⟨hFc, -, hlow, hder⟩ := hF
  have hE : 0 < 2 * exp eulerMascheroniConstant := by positivity
  have key : s * F s = 2 * exp eulerMascheroniConstant := by
    rcases le_or_gt s 2 with h2 | h2
    · rw [(hlow s (by linarith) h2).1]
      field_simp
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun v => v * F v)
        (fun v => f (v - 1)) h2
        (continuousOn_id.mul (hFc.mono fun x hx => mem_Ioi.2 (by linarith [hx.1])))
        (fun x hx => (hder x hx.1).1)
      have hf0 : f (c - 1) = 0 := (hlow (c - 1) (by linarith [hc.1]) (by linarith [hc.2])).2
      rw [hf0, eq_comm, div_eq_zero_iff] at hslope
      rcases hslope with h | h
      · have h2F : (2 : ℝ) * F 2 = 2 * exp eulerMascheroniConstant := by
          rw [(hlow 2 (by norm_num) le_rfl).1]; field_simp
        linarith
      · linarith
  unfold Wu04.normalized
  rw [key, div_self hE.ne']

/-- Comparison of sifted counts through their sifting conditions. -/
theorem S_le_of_sifted {A : Finset ℕ} {e D : ℕ} {y y' : ℝ}
    (h : ∀ a, Wu41.Sifted D y a → Wu41.Sifted D y' a) :
    Wu41.S A e D y ≤ Wu41.S A e D y' := by
  unfold Wu41.S
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2.1, h a ha.2.2⟩

/-- `S(A_e; P(D), y)` decreases as the sifting level `y` grows. -/
theorem S_anti {A : Finset ℕ} {e D : ℕ} {y y' : ℝ} (h : y ≤ y') :
    Wu41.S A e D y' ≤ Wu41.S A e D y :=
  S_le_of_sifted fun _ ha q hq hqy => ha q hq (hqy.trans_le h)

/-- Below `2` no prime sifts. -/
theorem S_low {A : Finset ℕ} {e D : ℕ} {y y' : ℝ} (hy : y ≤ 2) (hy' : y' ≤ 2) :
    Wu41.S A e D y = Wu41.S A e D y' := by
  have hv : ∀ (z : ℝ) (a : ℕ), z ≤ 2 → Wu41.Sifted D z a := fun z a hz q hq hqz => by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    linarith
  exact le_antisymm (S_le_of_sifted fun a _ => hv y' a hy')
    (S_le_of_sifted fun a _ => hv y a hy)

/-- For `x ≥ 0` and `1 ≤ s ≤ s'`, `S(A_e; P(D), x^{1/s}) ≤ S(A_e; P(D), x^{1/s'})`: Wu's
`Φ(N, σ, s)` increases with `s`, the fact behind the first sentence of the proof of
Corollary 1, page 13. -/
theorem S_rpow_mono {A : Finset ℕ} {e D : ℕ} {x s s' : ℝ} (hx : 0 ≤ x) (hs : 1 ≤ s)
    (hss : s ≤ s') :
    Wu41.S A e D (x ^ (1 / s)) ≤ Wu41.S A e D (x ^ (1 / s')) := by
  have hs0 : 0 < s := by linarith
  have hs'0 : 0 < s' := by linarith
  rcases le_or_gt 1 x with h1 | h1
  · apply S_anti
    exact Real.rpow_le_rpow_of_exponent_le h1 (one_div_le_one_div_of_le hs0 hss)
  · have e1 : x ^ (1 / s) < 1 := Real.rpow_lt_one hx h1 (by positivity)
    have e2 : x ^ (1 / s') < 1 := Real.rpow_lt_one hx h1 (by positivity)
    exact (S_low (by linarith) (by linarith)).le

theorem Phi_mono {δ : ℝ} {N i : ℕ} {V : Fin i → ℝ} {Δ s s' : ℝ} (hs : 1 ≤ s) (hss : s ≤ s') :
    Wu04.Phi δ N i V Δ s ≤ Wu04.Phi δ N i V Δ s' := by
  unfold Wu04.Phi
  apply Finset.sum_le_sum
  intro t _
  have hx : 0 ≤ Wu04.Q δ N / (Wu04.modulus t : ℝ) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  exact_mod_cast S_rpow_mono hx hs hss

/-- **Corollary 1 on `[1, 3]`, PROVED from the definitions.** Wu 2004 Corollary 1, page 13,
first sentence of the proof: `H_{k,N₀}(s)` is decreasing on `[1, 3]` since `A(s) = 1` there,
hence so is `H`. -/
theorem corollary1_low {F f : ℝ → ℝ} (hF : IsLinearSieve F f) {δ : ℝ} {H h : ℝ → ℝ}
    (hR : RepresentsCorrections F f δ H h) : AntitoneOn H (Icc (1 : ℝ) 3) := by
  intro a ha b hb hab
  have hE : Wu04.H F δ b ≤ Wu04.H F δ a := by
    apply iInf_mono
    intro k
    apply iSup_mono
    intro N₀
    apply sSup_le_sSup
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c, ?_, rfl⟩
    intro N hN h2 hEv i V Δ hU
    have := hc N hN h2 hEv i V Δ hU
    rw [normalized_eq_one hF hb.1 hb.2] at this
    rw [normalized_eq_one hF ha.1 ha.2]
    exact (Phi_mono ha.1 hab).trans this
  have h1 := (hR a ⟨ha.1, by linarith [ha.2]⟩).1
  have h2 := (hR b ⟨hb.1, by linarith [hb.2]⟩).1
  rw [← h1, ← h2] at hE
  exact_mod_cast hE

/-- SUB-LEAF of `corollary1` and of Lemma 6.1. Wu 2004 Proposition 2, page 11, second displayed
inequality, for `H`, which Wu says is established in the same way as the first, proved on pages
12 to 14 from Buchstab's identity 3.14 and the estimates 3.15 to 3.20:
for `2 ≤ s ≤ s' ≤ 10`, `H(s) ≥ H(s') + ∫_{s−1}^{s'−1} h(t)/t dt`. Cited. -/
theorem proposition2_H {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ s sp : ℝ, 2 ≤ s → s ≤ sp → sp ≤ 10 →
        H sp + (∫ t in (s - 1)..(sp - 1), h t / t) ≤ H s := by
  sorry

/-- SUB-LEAF of `lemma61_eq2` and `lemma61_eq3`. Wu 2004 Proposition 2, page 11, first displayed
inequality, for `h`, proved on pages 12 to 14 from Buchstab's identity 3.14 and the estimates 3.15
to 3.20: for `2 ≤ s ≤ s' ≤ 10`, `h(s) ≥ h(s') + ∫_{s−1}^{s'−1} H(t)/t dt`. Cited. -/
theorem proposition2_h {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ s sp : ℝ, 2 ≤ s → s ≤ sp → sp ≤ 10 →
        h sp + (∫ t in (s - 1)..(sp - 1), H t / t) ≤ h s := by
  sorry

/-- **Leaf `corollary1` from its split.** Wu 2004 Corollary 1, page 13: on `[1, 3]` from the
definitions, `corollary1_low`, PROVED; on `[3, 10]` from Propositions 2 and 1. Same statement
as `Burst4Split.corollary1`. CONDITIONAL ON `proposition2_H` and the Proposition 1
sub-leaves. -/
theorem corollary1 {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → AntitoneOn H (Icc (1 : ℝ) 10) := by
  obtain ⟨d1, hd1, h2⟩ := proposition2_H hF
  obtain ⟨d2, hd2, h1⟩ := proposition1 hF
  refine ⟨min d1 d2, lt_min hd1 hd2, fun δ hδ hδ' H h hR => ?_⟩
  have e1 : δ < d1 := hδ'.trans_le (min_le_left _ _)
  have e2 : δ < d2 := hδ'.trans_le (min_le_right _ _)
  have hlow := corollary1_low hF hR
  have hhigh : AntitoneOn H (Icc (3 : ℝ) 10) := by
    intro a ha b hb hab
    have := h2 δ hδ e1 H h hR a b (by linarith [ha.1]) hab hb.2
    have hint : 0 ≤ ∫ t in (a - 1)..(b - 1), h t / t := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro u hu
      have hu1 : 1 ≤ u := by linarith [hu.1, ha.1]
      exact div_nonneg (h1 δ hδ e2 H h hR u ⟨hu1, by linarith [hu.2, hb.2]⟩).2 (by linarith)
    linarith
  intro a ha b hb hab
  rcases le_total b 3 with hb3 | hb3
  · exact hlow ⟨ha.1, hab.trans hb3⟩ ⟨hb.1, hb3⟩ hab
  · rcases le_total a 3 with ha3 | ha3
    · exact (hhigh ⟨le_rfl, by norm_num⟩ ⟨hb3, hb.2⟩ hb3).trans
        (hlow ⟨ha.1, ha3⟩ ⟨by norm_num, le_rfl⟩ ha3)
    · exact hhigh ⟨ha3, ha.2⟩ ⟨hb3, hb.2⟩ hab

/-! ### Part C2. Lemma 6.1 from Proposition 2, page 28 -/

/-- The inputs of the proof of Lemma 6.1, page 28: Propositions 1 and 2 and Corollary 1. -/
structure L61Inputs (H h : ℝ → ℝ) : Prop where
  Hnn : ∀ s ∈ Icc (1 : ℝ) 10, 0 ≤ H s
  hnn : ∀ s ∈ Icc (1 : ℝ) 10, 0 ≤ h s
  Hanti : AntitoneOn H (Icc (1 : ℝ) 10)
  p2H : ∀ s sp : ℝ, 2 ≤ s → s ≤ sp → sp ≤ 10 → H sp + (∫ t in (s - 1)..(sp - 1), h t / t) ≤ H s
  p2h : ∀ s sp : ℝ, 2 ≤ s → s ≤ sp → sp ≤ 10 → h sp + (∫ t in (s - 1)..(sp - 1), H t / t) ≤ h s

/-- Fubini on `[α, β] × [1, 3]`. -/
theorem swap13 {α β : ℝ} (hαβ : α ≤ β) {F : ℝ → ℝ → ℝ}
    (hF : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc α β)).prod (volume.restrict (Ioc (1 : ℝ) 3)))) :
    ∫ u in α..β, (∫ t in (1 : ℝ)..3, F u t) = ∫ t in (1 : ℝ)..3, ∫ u in α..β, F u t := by
  simp only [intervalIntegral.integral_of_le hαβ,
    intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  exact MeasureTheory.integral_integral_swap hF

/-- `∫₁³ K(t) 1_{t ≥ c} dt = ∫_c^3 K` for `1 ≤ c ≤ 3`. -/
theorem integral_ind_ge {K : ℝ → ℝ} {c : ℝ} (hc1 : 1 ≤ c) (hc3 : c ≤ 3)
    (hK : IntervalIntegrable K volume 1 3) :
    (∫ t in (1 : ℝ)..3, K t * (if c ≤ t then 1 else 0)) = ∫ t in c..3, K t := by
  have h1 : IntervalIntegrable K volume 1 c := hK.mono_set (by
    rw [uIcc_of_le hc1, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]; exact Icc_subset_Icc le_rfl hc3)
  have h2 : IntervalIntegrable K volume c 3 := hK.mono_set (by
    rw [uIcc_of_le hc3, uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]; exact Icc_subset_Icc hc1 le_rfl)
  have e : (fun t => K t * (if c ≤ t then 1 else 0)) =
      fun t => K t - K t * (if t ≤ c then 1 else 0) + K t * (if t = c then 1 else 0) := by
    funext t
    by_cases h : t = c
    · subst h; simp
    · rcases lt_or_gt_of_ne h with h' | h'
      · simp [h, h'.le, not_le.2 h']
      · simp [h, h'.le, not_le.2 h']
  have hz : (∫ t in (1 : ℝ)..3, K t * (if t = c then 1 else 0)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    have : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ c := by
      simpa using (measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := c)))
    filter_upwards [this] with t ht _
    simp [ht]
  have hind : (∫ t in (1 : ℝ)..3, K t * (if t ≤ c then 1 else 0)) = ∫ t in (1 : ℝ)..c, K t := by
    have e2 : (fun t => K t * (if t ≤ c then 1 else 0)) = {x | x ≤ c}.indicator K := by
      funext t
      by_cases h : t ≤ c
      · simp [h, indicator_of_mem (show t ∈ {x | x ≤ c} from h)]
      · simp [h, indicator_of_notMem (show t ∉ {x | x ≤ c} from h)]
    rw [e2]
    exact intervalIntegral.integral_indicator ⟨hc1, hc3⟩
  have hKi : IntervalIntegrable (fun t => K t * (if t ≤ c then 1 else 0)) volume 1 3 := by
    have e2 : (fun t => K t * (if t ≤ c then 1 else 0)) = {x | x ≤ c}.indicator K := by
      funext t
      by_cases h : t ≤ c
      · simp [h, indicator_of_mem (show t ∈ {x | x ≤ c} from h)]
      · simp [h, indicator_of_notMem (show t ∉ {x | x ≤ c} from h)]
    rw [e2]
    rw [intervalIntegrable_iff] at hK ⊢
    exact hK.indicator measurableSet_Iic
  have hKz : IntervalIntegrable (fun t => K t * (if t = c then 1 else 0)) volume 1 3 := by
    have e3 : (fun t => K t * (if t = c then 1 else 0)) = ({c} : Set ℝ).indicator K := by
      funext t
      by_cases h : t = c
      · subst h; simp
      · simp [h]
    rw [e3]
    rw [intervalIntegrable_iff] at hK ⊢
    exact hK.indicator (measurableSet_singleton c)
  rw [e, intervalIntegral.integral_add (hK.sub hKi) hKz, intervalIntegral.integral_sub hK hKi,
    hz, hind, ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  ring

/-- `∫_a^b f(u) 1_{u ≤ c} du = ∫_a^c f` for `a ≤ c ≤ b`. -/
theorem integral_ind_le {f : ℝ → ℝ} {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    (∫ u in a..b, f u * (if u ≤ c then 1 else 0)) = ∫ u in a..c, f u := by
  have e2 : (fun u => f u * (if u ≤ c then 1 else 0)) = {x | x ≤ c}.indicator f := by
    funext t
    by_cases h : t ≤ c
    · simp [h, indicator_of_mem (show t ∈ {x | x ≤ c} from h)]
    · simp [h, indicator_of_notMem (show t ∉ {x | x ≤ c} from h)]
  rw [e2]
  exact intervalIntegral.integral_indicator ⟨hac, hcb⟩

/-- `u ↦ F(u)/u` is decreasing when `F ≥ 0` is decreasing and `u > 0`. -/
theorem antitoneOn_div_id {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hF0 : ∀ u ∈ Icc a b, 0 ≤ F u)
    (hF : AntitoneOn F (Icc a b)) : AntitoneOn (fun u => F u / u) (Icc a b) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := ha.trans_le hx.1
  exact div_le_div₀ (hF0 x hx) (hF hx hy hxy) hx0 hxy

/-- `H(t)/t` is integrable on `[1, 3]` for `H` decreasing there. -/
theorem H_div_integrable {H : ℝ → ℝ} (hH : AntitoneOn H (Icc (1 : ℝ) 3)) :
    IntervalIntegrable (fun t => H t / t) volume 1 3 := by
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc 1 3) := by
    apply continuousOn_inv₀.mono
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
  have := (Burst4Split.product_integrable hH
    (intervalIntegrable_const (c := (1 : ℝ)))).mul_continuousOn hc
  simpa [div_eq_mul_inv] using this

/-- Display 6.4 of the proof of Lemma 6.1, page 28: for `3 ≤ s' ≤ 5`,
`H(s') ≥ h(4) log(4/(s'−1)) + ∫₁³ H(t) 1_{[s'−2,3]}(t)/t · log((t+1)/(s'−1)) dt`.
PROVED from Propositions 1 and 2 and Corollary 1, through `L61Inputs`. -/
theorem eq64 {H h : ℝ → ℝ} (hI : L61Inputs H h) {sp : ℝ} (h3 : 3 ≤ sp) (h5 : sp ≤ 5) :
    h 4 * log (4 / (sp - 1)) +
        (∫ t in (1 : ℝ)..3, H t * (ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1)))) ≤
      H sp := by
  have hH13 : AntitoneOn H (Icc (1 : ℝ) 3) := hI.Hanti.mono (Icc_subset_Icc le_rfl (by norm_num))
  have hKint := H_div_integrable hH13
  have hsp1 : 0 < sp - 1 := by linarith
  set G : ℝ → ℝ := fun u => ∫ t in (u - 1)..3, H t / t with hGdef
  have A1 : (∫ u in (sp - 1)..4, h u / u) ≤ H sp := by
    have := hI.p2H sp 5 (by linarith) h5 (by norm_num)
    have hH5 := hI.Hnn 5 ⟨by norm_num, by norm_num⟩
    rw [show (5 : ℝ) - 1 = 4 by norm_num] at this
    linarith
  have Hdiv_nn : ∀ t, 1 ≤ t → t ≤ 10 → 0 ≤ H t / t := fun t h1 h10 =>
    div_nonneg (hI.Hnn t ⟨h1, h10⟩) (by linarith)
  have Gnn : ∀ u ∈ Icc (sp - 1) 4, 0 ≤ G u := fun u hu =>
    intervalIntegral.integral_nonneg (by linarith [hu.2])
      (fun t ht => Hdiv_nn t (by linarith [ht.1, hu.1]) (by linarith [ht.2]))
  have Ganti : AntitoneOn G (Icc (sp - 1) 4) := by
    intro x hx y hy hxy
    have hi1 : IntervalIntegrable (fun t => H t / t) volume (x - 1) (y - 1) :=
      hKint.mono_set (by
        rw [uIcc_of_le (by linarith), uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
        exact Icc_subset_Icc (by linarith [hx.1]) (by linarith [hy.2]))
    have hi2 : IntervalIntegrable (fun t => H t / t) volume (y - 1) 3 :=
      hKint.mono_set (by
        rw [uIcc_of_le (by linarith [hy.2]), uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
        exact Icc_subset_Icc (by linarith [hy.1]) le_rfl)
    have hsum := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hnn : 0 ≤ ∫ t in (x - 1)..(y - 1), H t / t :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun t ht => Hdiv_nn t (by linarith [ht.1, hx.1]) (by linarith [ht.2, hy.2]))
    show G y ≤ G x
    simp only [hGdef]
    linarith
  have hanti : AntitoneOn h (Icc (2 : ℝ) 10) := by
    intro x hx y hy hxy
    have := hI.p2h x y hx.1 hxy hy.2
    have : 0 ≤ ∫ t in (x - 1)..(y - 1), H t / t :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun t ht => Hdiv_nn t (by linarith [ht.1, hx.1]) (by linarith [ht.2, hy.2]))
    linarith
  have A2 : ∀ u ∈ Icc (sp - 1) 4, (h 4 + G u) / u ≤ h u / u := by
    intro u hu
    have := hI.p2h u 4 (by linarith [hu.1]) hu.2 (by norm_num)
    rw [show (4 : ℝ) - 1 = 3 by norm_num] at this
    exact div_le_div_of_nonneg_right (by simp only [hGdef]; linarith) (by linarith [hu.1])
  have h4nn : 0 ≤ h 4 := hI.hnn 4 ⟨by norm_num, by norm_num⟩
  have iL : IntervalIntegrable (fun u => (h 4 + G u) / u) volume (sp - 1) 4 := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    apply antitoneOn_div_id hsp1 (fun u hu => by linarith [Gnn u hu])
    intro x hx y hy hxy
    simp only
    linarith [Ganti hx hy hxy]
  have iR : IntervalIntegrable (fun u => h u / u) volume (sp - 1) 4 := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact antitoneOn_div_id hsp1 (fun u hu => hI.hnn u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (hanti.mono (Icc_subset_Icc (by linarith) (by norm_num)))
  have A3 := intervalIntegral.integral_mono_on (by linarith) iL iR A2
  have iG : IntervalIntegrable (fun u => G u / u) volume (sp - 1) 4 := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact antitoneOn_div_id hsp1 Gnn Ganti
  have iinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume (sp - 1) 4 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    exact (show (0 : ℝ) < u by linarith [hu.1]).ne'
  have A4 : (∫ u in (sp - 1)..4, (h 4 + G u) / u) =
      h 4 * log (4 / (sp - 1)) + ∫ u in (sp - 1)..4, G u / u := by
    have e : (fun u => (h 4 + G u) / u) = fun u => h 4 * u⁻¹ + G u / u := by
      funext u; ring
    rw [e, intervalIntegral.integral_add (iinv.const_mul _) iG,
      intervalIntegral.integral_const_mul, integral_inv_of_pos hsp1 (by norm_num)]
  have A5 : (∫ u in (sp - 1)..4, G u / u) =
      ∫ t in (1 : ℝ)..3, H t * (ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1))) := by
    let S : Set (ℝ × ℝ) := {z | z.1 - 1 ≤ z.2}
    let F : ℝ → ℝ → ℝ := fun u t => S.indicator (fun z => z.1⁻¹ * (H z.2 / z.2)) (u, t)
    have hF : ∀ u t, F u t = u⁻¹ * (H t / t) * (if u - 1 ≤ t then 1 else 0) := by
      intro u t
      by_cases hh : u - 1 ≤ t
      · rw [show F u t = _ from indicator_of_mem (show (u, t) ∈ S from hh) _]; simp [hh]
      · rw [show F u t = _ from indicator_of_notMem (show (u, t) ∉ S from hh) _]; simp [hh]
    have step1 : ∀ u ∈ uIcc (sp - 1) 4, G u / u = ∫ t in (1 : ℝ)..3, F u t := by
      intro u hu
      rw [uIcc_of_le (by linarith)] at hu
      simp only [hF]
      have e : (fun t => u⁻¹ * (H t / t) * (if u - 1 ≤ t then 1 else 0)) =
          fun t => u⁻¹ * ((H t / t) * (if u - 1 ≤ t then 1 else 0)) := by
        funext t; ring
      rw [e, intervalIntegral.integral_const_mul,
        integral_ind_ge (by linarith [hu.1]) (by linarith [hu.2]) hKint]
      simp only [hGdef]
      ring
    have hint : Integrable (Function.uncurry F)
        ((volume.restrict (Ioc (sp - 1) 4)).prod (volume.restrict (Ioc (1 : ℝ) 3))) := by
      have hf : Integrable (fun u : ℝ => u⁻¹) (volume.restrict (Ioc (sp - 1) 4)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 iinv
      have hg : Integrable (fun t : ℝ => H t / t) (volume.restrict (Ioc (1 : ℝ) 3)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hKint
      exact (hf.mul_prod hg).indicator
        (measurableSet_le (measurable_fst.sub_const 1) measurable_snd)
    rw [intervalIntegral.integral_congr step1, swap13 (by linarith) hint]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    simp only [hF]
    have e : (fun u => u⁻¹ * (H t / t) * (if u - 1 ≤ t then 1 else 0)) =
        fun u => (H t / t) * (u⁻¹ * (if u ≤ t + 1 then 1 else 0)) := by
      funext u
      have hiff : (u - 1 ≤ t) ↔ (u ≤ t + 1) := by constructor <;> intro <;> linarith
      simp only [hiff]
      ring
    rw [e, intervalIntegral.integral_const_mul]
    by_cases hts : sp - 2 ≤ t
    · rw [integral_ind_le (f := fun u : ℝ => u⁻¹) (by linarith) (by linarith [ht.2]),
        integral_inv_of_pos hsp1 (by linarith [ht.1])]
      simp only [ind, if_pos (show sp - 2 ≤ t ∧ t ≤ 3 from ⟨hts, ht.2⟩)]
      ring
    · have hz : (∫ u in (sp - 1)..4, u⁻¹ * (if u ≤ t + 1 then 1 else 0)) = 0 := by
        apply intervalIntegral.integral_zero_ae
        filter_upwards with u hu
        rw [uIoc_of_le (by linarith)] at hu
        have : ¬ u ≤ t + 1 := by
          intro hle
          exact hts (by linarith [hu.1])
        simp [this]
      rw [hz]
      simp only [ind, if_neg (show ¬(sp - 2 ≤ t ∧ t ≤ 3) from fun hh => hts hh.1)]
      ring
  calc h 4 * log (4 / (sp - 1)) +
        (∫ t in (1 : ℝ)..3, H t * (ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1))))
        = ∫ u in (sp - 1)..4, (h 4 + G u) / u := by rw [A4, A5]
    _ ≤ ∫ u in (sp - 1)..4, h u / u := A3
    _ ≤ H sp := A1

/-- Display 6.1 of Lemma 6.1, page 28: `h(4) ≥ ∫₁³ H(t) σ₀(t)/t dt`. PROVED from Propositions
1 and 2 and Corollary 1, through `L61Inputs` and display 6.4, `eq64`. -/
theorem eq61 {H h : ℝ → ℝ} (hI : L61Inputs H h) :
    (∫ t in (1 : ℝ)..3, H t * (sigma0 t / t)) ≤ h 4 := by
  have hH13 : AntitoneOn H (Icc (1 : ℝ) 3) := hI.Hanti.mono (Icc_subset_Icc le_rfl (by norm_num))
  have hKint := H_div_integrable hH13
  have h4nn : 0 ≤ h 4 := hI.hnn 4 ⟨by norm_num, by norm_num⟩
  set J : ℝ → ℝ := fun v =>
    ∫ t in (1 : ℝ)..3, H t * (ind (v - 2) 3 t / t * log ((t + 1) / (v - 1))) with hJdef
  have hd : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [Wu04Integral.sigma_denominator_bounds.1]
  -- B1
  have B1 : (∫ v in (3 : ℝ)..5, H v / v) ≤ h 4 := by
    have := hI.p2h 4 6 (by norm_num) (by norm_num) (by norm_num)
    have h6 := hI.hnn 6 ⟨by norm_num, by norm_num⟩
    rw [show (4 : ℝ) - 1 = 3 by norm_num, show (6 : ℝ) - 1 = 5 by norm_num] at this
    linarith
  -- the kernel of 6.4 and its properties
  have kint : ∀ v, 3 ≤ v → v ≤ 5 → IntervalIntegrable
      (fun t => ind (v - 2) 3 t / t * log ((t + 1) / (v - 1))) volume 1 3 := by
    intro v hv3 hv5
    apply ind_log_integrable (by fun_prop)
      (fun t ht => (show (0 : ℝ) < t by linarith [ht.2.1]).ne') (by fun_prop)
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) (by linarith)).ne'
  have kval : ∀ v t, 3 ≤ v → 1 ≤ t → 0 ≤ ind (v - 2) 3 t / t * log ((t + 1) / (v - 1)) := by
    intro v t hv ht
    by_cases hi : v - 2 ≤ t ∧ t ≤ 3
    · rw [ind, if_pos hi]
      exact mul_nonneg (div_nonneg (by norm_num) (by linarith))
        (Real.log_nonneg ((one_le_div (by linarith)).2 (by linarith [hi.1])))
    · rw [ind, if_neg hi]; simp
  have kanti : ∀ v w t, 3 ≤ v → v ≤ w → 1 ≤ t →
      ind (w - 2) 3 t / t * log ((t + 1) / (w - 1)) ≤
        ind (v - 2) 3 t / t * log ((t + 1) / (v - 1)) := by
    intro v w t hv hvw ht
    by_cases hw : w - 2 ≤ t ∧ t ≤ 3
    · have hv' : v - 2 ≤ t ∧ t ≤ 3 := ⟨by linarith [hw.1], hw.2⟩
      rw [ind, if_pos hw, ind, if_pos hv']
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (by linarith))
      exact Real.log_le_log (div_pos (by linarith) (by linarith))
        (div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith))
    · rw [ind, if_neg hw]; simpa using kval v t hv ht
  have Hnn13 : ∀ t ∈ Icc (1 : ℝ) 3, 0 ≤ H t := fun t ht => hI.Hnn t ⟨ht.1, by linarith [ht.2]⟩
  have Jnn : ∀ v ∈ Icc (3 : ℝ) 5, 0 ≤ J v := fun v hv =>
    intervalIntegral.integral_nonneg (by norm_num)
      (fun t ht => mul_nonneg (Hnn13 t ht) (kval v t hv.1 ht.1))
  have Janti : AntitoneOn J (Icc (3 : ℝ) 5) := by
    intro v hv w hw hvw
    apply intervalIntegral.integral_mono_on (by norm_num)
      (Burst4Split.product_integrable hH13 (kint w hw.1 hw.2))
      (Burst4Split.product_integrable hH13 (kint v hv.1 hv.2))
    intro t ht
    exact mul_le_mul_of_nonneg_left (kanti v w t hv.1 hvw ht.1) (Hnn13 t ht)
  -- the logarithmic coefficient
  have Lnn : ∀ v ∈ Icc (3 : ℝ) 5, 0 ≤ log (4 / (v - 1)) := fun v hv =>
    Real.log_nonneg ((one_le_div (by linarith [hv.1])).2 (by linarith [hv.2]))
  have Lanti : AntitoneOn (fun v => log (4 / (v - 1))) (Icc (3 : ℝ) 5) := by
    intro v hv w hw hvw
    exact Real.log_le_log (div_pos (by norm_num) (by linarith [hw.1]))
      (div_le_div_of_nonneg_left (by norm_num) (by linarith [hv.1]) (by linarith))
  -- B3
  have iL : IntervalIntegrable (fun v => (h 4 * log (4 / (v - 1)) + J v) / v) volume 3 5 := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    apply antitoneOn_div_id (by norm_num)
      (fun v hv => add_nonneg (mul_nonneg h4nn (Lnn v hv)) (Jnn v hv))
    intro v hv w hw hvw
    simp only
    have := mul_le_mul_of_nonneg_left (Lanti hv hw hvw) h4nn
    linarith [Janti hv hw hvw]
  have iR : IntervalIntegrable (fun v => H v / v) volume 3 5 := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact antitoneOn_div_id (by norm_num) (fun v hv => hI.Hnn v ⟨by linarith [hv.1], by linarith [hv.2]⟩)
      (hI.Hanti.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
  have B3 := intervalIntegral.integral_mono_on (by norm_num) iL iR (fun v hv =>
    div_le_div_of_nonneg_right (eq64 hI hv.1 hv.2) (by linarith [hv.1]))
  -- B4
  have iJ : IntervalIntegrable (fun v => J v / v) volume 3 5 := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact antitoneOn_div_id (by norm_num) Jnn Janti
  have iS : IntervalIntegrable (fun v => log (4 / (v - 1)) / v) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    apply ContinuousOn.div _ continuousOn_id (fun v hv => (show (0 : ℝ) < v by linarith [hv.1]).ne')
    apply ContinuousOn.log (ContinuousOn.div continuousOn_const (by fun_prop)
      (fun v hv => (show (0 : ℝ) < v - 1 by linarith [hv.1]).ne'))
    intro v hv
    exact (div_pos (by norm_num) (show (0 : ℝ) < v - 1 by linarith [hv.1])).ne'
  have B4 : (∫ v in (3 : ℝ)..5, (h 4 * log (4 / (v - 1)) + J v) / v) =
      h 4 * Wu04Integral.sigma 3 5 4 + ∫ v in (3 : ℝ)..5, J v / v := by
    have e : (fun v => (h 4 * log (4 / (v - 1)) + J v) / v) =
        fun v => h 4 * (log (4 / (v - 1)) / v) + J v / v := by
      funext v; ring
    rw [e, intervalIntegral.integral_add (iS.const_mul _) iJ, intervalIntegral.integral_const_mul]
    rfl
  -- B5, the interchange
  have iinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    exact (show (0 : ℝ) < u by linarith [hu.1]).ne'
  have B5 : (∫ v in (3 : ℝ)..5, J v / v) =
      ∫ t in (1 : ℝ)..3, H t * (Wu04Integral.sigma 3 (t + 2) (t + 1) / t) := by
    let S : Set (ℝ × ℝ) := {z | z.1 - 2 ≤ z.2 ∧ z.2 ≤ 3}
    let F : ℝ → ℝ → ℝ := fun v t =>
      S.indicator (fun z => z.1⁻¹ * (H z.2 / z.2 * log (z.2 + 1))) (v, t) -
        S.indicator (fun z => z.1⁻¹ * log (z.1 - 1) * (H z.2 / z.2)) (v, t)
    have hF : ∀ v t, 3 ≤ v → 1 ≤ t → F v t =
        v⁻¹ * (H t * (ind (v - 2) 3 t / t * log ((t + 1) / (v - 1)))) := by
      intro v t hv ht
      by_cases hh : v - 2 ≤ t ∧ t ≤ 3
      · simp only [F, indicator_of_mem (show (v, t) ∈ S from hh), ind, if_pos hh]
        rw [Real.log_div (by linarith) (by linarith)]
        ring
      · simp only [F, indicator_of_notMem (show (v, t) ∉ S from hh), ind, if_neg hh]
        ring
    have step1 : ∀ v ∈ uIcc (3 : ℝ) 5, J v / v = ∫ t in (1 : ℝ)..3, F v t := by
      intro v hv
      rw [uIcc_of_le (by norm_num)] at hv
      rw [intervalIntegral.integral_congr (g := fun t =>
          v⁻¹ * (H t * (ind (v - 2) 3 t / t * log ((t + 1) / (v - 1))))) (fun t ht => by
        rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
        exact hF v t hv.1 ht.1)]
      rw [intervalIntegral.integral_const_mul]
      simp only [hJdef]
      ring
    have hint : Integrable (Function.uncurry F)
        ((volume.restrict (Ioc (3 : ℝ) 5)).prod (volume.restrict (Ioc (1 : ℝ) 3))) := by
      have hf1 : Integrable (fun u : ℝ => u⁻¹) (volume.restrict (Ioc (3 : ℝ) 5)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 iinv
      have hlog : IntervalIntegrable (fun u : ℝ => u⁻¹ * log (u - 1)) volume 3 5 := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (by norm_num)]
        apply ContinuousOn.mul (continuousOn_inv₀.mono fun u hu =>
          (show (0 : ℝ) < u by linarith [hu.1]).ne')
        exact ContinuousOn.log (by fun_prop)
          (fun u hu => (show (0 : ℝ) < u - 1 by linarith [hu.1]).ne')
      have hf2 : Integrable (fun u : ℝ => u⁻¹ * log (u - 1)) (volume.restrict (Ioc (3 : ℝ) 5)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hlog
      have hg1i : IntervalIntegrable (fun t => H t / t * log (t + 1)) volume 1 3 := by
        apply hKint.mul_continuousOn
        apply ContinuousOn.log (by fun_prop)
        intro t ht
        rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
        exact (show (0 : ℝ) < t + 1 by linarith [ht.1]).ne'
      have hg1 : Integrable (fun t : ℝ => H t / t * log (t + 1))
          (volume.restrict (Ioc (1 : ℝ) 3)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hg1i
      have hg2 : Integrable (fun t : ℝ => H t / t) (volume.restrict (Ioc (1 : ℝ) 3)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hKint
      have hS : MeasurableSet S :=
        (measurableSet_le (measurable_fst.sub_const 2) measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)
      exact ((hf1.mul_prod hg1).indicator hS).sub ((hf2.mul_prod hg2).indicator hS)
    rw [intervalIntegral.integral_congr step1, swap13 (by norm_num) hint]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    show (∫ v in (3 : ℝ)..5, F v t) = H t * (Wu04Integral.sigma 3 (t + 2) (t + 1) / t)
    rw [intervalIntegral.integral_congr (g := fun v =>
        H t / t * (log ((t + 1) / (v - 1)) / v * (if v ≤ t + 2 then 1 else 0))) (fun v hv => by
      rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at hv
      rw [hF v t hv.1 ht.1]
      by_cases hh : v ≤ t + 2
      · have hi : v - 2 ≤ t ∧ t ≤ 3 := ⟨by linarith, ht.2⟩
        simp only [ind, if_pos hi, if_pos hh]
        ring
      · have hi : ¬ (v - 2 ≤ t ∧ t ≤ 3) := fun h' => hh (by linarith [h'.1])
        simp only [ind, if_neg hi, if_neg hh]
        ring)]
    rw [intervalIntegral.integral_const_mul,
      integral_ind_le (f := fun v => log ((t + 1) / (v - 1)) / v) (by linarith [ht.1])
        (by linarith [ht.2])]
    simp only [Wu04Integral.sigma]
    ring
  -- B6
  have key : h 4 * Wu04Integral.sigma 3 5 4 + (∫ t in (1 : ℝ)..3, H t * (Wu04Integral.sigma 3 (t + 2) (t + 1) / t))
      ≤ h 4 := by
    have := B3
    rw [B4, B5] at this
    linarith
  have e : (∫ t in (1 : ℝ)..3, H t * (sigma0 t / t)) =
      (∫ t in (1 : ℝ)..3, H t * (Wu04Integral.sigma 3 (t + 2) (t + 1) / t)) / (1 - Wu04Integral.sigma 3 5 4) := by
    rw [eq_div_iff hd.ne', ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Wu04Integral.sigma0]
    field_simp
  rw [e, div_le_iff₀ hd]
  linarith

/-- Display 6.2 of Lemma 6.1, page 28, from 6.4 and 6.1. PROVED through `L61Inputs`. -/
theorem eq62 {H h : ℝ → ℝ} (hI : L61Inputs H h) {sp : ℝ} (h3 : 3 ≤ sp) (h5 : sp ≤ 5) :
    (∫ t in (1 : ℝ)..3, H t * (sigma0 t / t * log (4 / (sp - 1)) +
      ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1)))) ≤ H sp := by
  have hH13 : AntitoneOn H (Icc (1 : ℝ) 3) := hI.Hanti.mono (Icc_subset_Icc le_rfl (by norm_num))
  have i1 : IntervalIntegrable (fun t => H t * (sigma0 t / t)) volume 1 3 := by
    apply Burst4Split.product_integrable hH13
    have := sigma_term_integrable 1 1 one_pos
    simpa only [one_mul, mul_one] using this
  have i2 : IntervalIntegrable (fun t => H t * (ind (sp - 2) 3 t / t *
      log ((t + 1) / (sp - 1)))) volume 1 3 := by
    apply Burst4Split.product_integrable hH13
    apply ind_log_integrable (by fun_prop)
      (fun t ht => (show (0 : ℝ) < t by linarith [ht.2.1]).ne') (by fun_prop)
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) (by linarith)).ne'
  have e : (fun t => H t * (sigma0 t / t * log (4 / (sp - 1)) +
      ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1)))) =
      fun t => log (4 / (sp - 1)) * (H t * (sigma0 t / t)) +
        H t * (ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1))) := by
    funext t; ring
  rw [e, intervalIntegral.integral_add (i1.const_mul _) i2, intervalIntegral.integral_const_mul]
  have hL : 0 ≤ log (4 / (sp - 1)) :=
    Real.log_nonneg ((one_le_div (by linarith)).2 (by linarith))
  have h61 := mul_le_mul_of_nonneg_left (eq61 hI) hL
  have h64 := eq64 hI h3 h5
  linarith

/-- `∫_a^x dt/(t(1−t)) = log((x − ax)/(a − ax))` for `0 < a ≤ x < 1`, the integral used for
display 6.3 on page 28. -/
theorem w_integral {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hx : x < 1) :
    (∫ t in a..x, (t * (1 - t))⁻¹) = log ((x - a * x) / (a - a * x)) := by
  have hderiv : ∀ t ∈ uIcc a x,
      HasDerivAt (fun t => log t - log (1 - t)) ((t * (1 - t))⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hax] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    have h1 := Real.hasDerivAt_log ht0.ne'
    have h2 := ((hasDerivAt_id t).const_sub 1).log (by simp only [id]; exact ht1.ne')
    have ht0' := ht0.ne'
    have ht1' := ht1.ne'
    convert h1.sub h2 using 1
    · funext y; simp
    · simp only [id]
      field_simp
      ring
  have hint : IntervalIntegrable (fun t => (t * (1 - t))⁻¹) volume a x := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    rw [uIcc_of_le hax] at ht
    exact (mul_pos (ha.trans_le ht.1) (by linarith [ht.2])).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hx0 : 0 < x := ha.trans_le hax
  rw [show x - a * x = x * (1 - a) by ring, show a - a * x = a * (1 - x) by ring,
    log_div (mul_pos hx0 (by linarith)).ne' (mul_pos ha (by linarith)).ne',
    log_mul hx0.ne' (by linarith), log_mul ha.ne' (by linarith)]
  ring

/-- Display 6.3 of Lemma 6.1, page 28. PROVED, as Wu does, from Proposition 2 and display 6.1,
through `L61Inputs`. -/
theorem eq63 {H h : ℝ → ℝ} (hI : L61Inputs H h) {a b c : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < 1) (hac : 2 ≤ a * c) (habc : a * c < b * c) (hbc : b * c ≤ 4) :
    log ((b - a * b) / (a - a * b)) *
        (∫ t in (1 : ℝ)..3, H t * ((sigma0 t + ind (b * c - 1) 3 t) / t)) +
      (∫ t in (1 : ℝ)..3, H t * (ind (a * c - 1) (b * c - 1) t / t *
        log ((1 - a) * (t + 1) / (a * (c - 1 - t))))) ≤
      ∫ t in a..b, h (c * t) / (t * (1 - t)) := by
  have hH13 : AntitoneOn H (Icc (1 : ℝ) 3) := hI.Hanti.mono (Icc_subset_Icc le_rfl (by norm_num))
  have hKint := H_div_integrable hH13
  have h4nn : 0 ≤ h 4 := hI.hnn 4 ⟨by norm_num, by norm_num⟩
  have hc0 : 0 < c := by
    by_contra hc
    have : a * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le (not_lt.1 hc)
    linarith
  have hab' : a ≤ b := hab.le
  set L := log ((b - a * b) / (a - a * b)) with hLdef
  have hLeq : (∫ t in a..b, (t * (1 - t))⁻¹) = L := w_integral ha hab' hb
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg
    rw [one_le_div (by nlinarith)]
    nlinarith
  set G : ℝ → ℝ := fun u => ∫ τ in (u - 1)..3, H τ / τ with hGdef
  have hct : ∀ t ∈ Icc a b, 2 ≤ c * t ∧ c * t ≤ 4 := fun t ht =>
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have Hdiv_nn : ∀ t, 1 ≤ t → t ≤ 10 → 0 ≤ H t / t := fun t h1 h10 =>
    div_nonneg (hI.Hnn t ⟨h1, h10⟩) (by linarith)
  have hanti : AntitoneOn h (Icc (2 : ℝ) 10) := by
    intro x hx y hy hxy
    have := hI.p2h x y hx.1 hxy hy.2
    have : 0 ≤ ∫ t in (x - 1)..(y - 1), H t / t :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun t ht => Hdiv_nn t (by linarith [ht.1, hx.1]) (by linarith [ht.2, hy.2]))
    linarith
  have Gnn : ∀ u ∈ Icc (2 : ℝ) 4, 0 ≤ G u := fun u hu =>
    intervalIntegral.integral_nonneg (by linarith [hu.2])
      (fun t ht => Hdiv_nn t (by linarith [ht.1, hu.1]) (by linarith [ht.2]))
  have Ganti : AntitoneOn G (Icc (2 : ℝ) 4) := by
    intro x hx y hy hxy
    have hi1 : IntervalIntegrable (fun t => H t / t) volume (x - 1) (y - 1) :=
      hKint.mono_set (by
        rw [uIcc_of_le (by linarith), uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
        exact Icc_subset_Icc (by linarith [hx.1]) (by linarith [hy.2]))
    have hi2 : IntervalIntegrable (fun t => H t / t) volume (y - 1) 3 :=
      hKint.mono_set (by
        rw [uIcc_of_le (by linarith [hy.2]), uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
        exact Icc_subset_Icc (by linarith [hy.1]) le_rfl)
    have hsum := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hnn : 0 ≤ ∫ t in (x - 1)..(y - 1), H t / t :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun t ht => Hdiv_nn t (by linarith [ht.1, hx.1]) (by linarith [ht.2, hy.2]))
    show G y ≤ G x
    simp only [hGdef]
    linarith
  -- integrability on `[a, b]`
  have hw : ContinuousOn (fun t : ℝ => (t * (1 - t))⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    rw [uIcc_of_le hab'] at ht
    exact (mul_pos (ha.trans_le ht.1) (by linarith [ht.2])).ne'
  have iW : IntervalIntegrable (fun t : ℝ => (t * (1 - t))⁻¹) volume a b :=
    hw.intervalIntegrable
  have hcomp : ∀ t₁ ∈ Icc a b, ∀ t₂ ∈ Icc a b, t₁ ≤ t₂ → c * t₁ ≤ c * t₂ :=
    fun _ _ _ _ h12 => mul_le_mul_of_nonneg_left h12 hc0.le
  have iR : IntervalIntegrable (fun t => h (c * t) * (t * (1 - t))⁻¹) volume a b := by
    apply IntervalIntegrable.mul_continuousOn _ hw
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hab']
    intro x hx y hy hxy
    exact hanti ⟨(hct x hx).1, by linarith [(hct x hx).2]⟩
      ⟨(hct y hy).1, by linarith [(hct y hy).2]⟩ (hcomp x hx y hy hxy)
  have iG : IntervalIntegrable (fun t => G (c * t) * (t * (1 - t))⁻¹) volume a b := by
    apply IntervalIntegrable.mul_continuousOn _ hw
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hab']
    intro x hx y hy hxy
    exact Ganti (hct x hx) (hct y hy) (hcomp x hx y hy hxy)
  have eL : (fun t => (h 4 + G (c * t)) * (t * (1 - t))⁻¹) =
      fun t => h 4 * (t * (1 - t))⁻¹ + G (c * t) * (t * (1 - t))⁻¹ := by
    funext t; ring
  have iL : IntervalIntegrable (fun t => (h 4 + G (c * t)) * (t * (1 - t))⁻¹) volume a b := by
    rw [eL]; exact (iW.const_mul _).add iG
  -- C1 and C2
  have C1 := intervalIntegral.integral_mono_on hab' iL iR (fun t ht => by
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 (mul_pos (ha.trans_le ht.1)
      (by linarith [ht.2])).le)
    have := hI.p2h (c * t) 4 (hct t ht).1 (hct t ht).2 (by norm_num)
    rw [show (4 : ℝ) - 1 = 3 by norm_num] at this
    simp only [hGdef]
    linarith)
  have C2 : (∫ t in a..b, (h 4 + G (c * t)) * (t * (1 - t))⁻¹) =
      h 4 * L + ∫ t in a..b, G (c * t) * (t * (1 - t))⁻¹ := by
    rw [eL, intervalIntegral.integral_add (iW.const_mul _) iG,
      intervalIntegral.integral_const_mul, hLeq]
  -- C4, the interchange
  set Inner : ℝ → ℝ := fun τ =>
    ∫ t in a..b, (t * (1 - t))⁻¹ * (if t ≤ (τ + 1) / c then 1 else 0) with hInner
  have C4 : (∫ t in a..b, G (c * t) * (t * (1 - t))⁻¹) =
      ∫ τ in (1 : ℝ)..3, H τ / τ * Inner τ := by
    let S : Set (ℝ × ℝ) := {z | c * z.1 - 1 ≤ z.2}
    let F : ℝ → ℝ → ℝ := fun t τ =>
      S.indicator (fun z => (z.1 * (1 - z.1))⁻¹ * (H z.2 / z.2)) (t, τ)
    have hiff : ∀ t τ, (c * t - 1 ≤ τ) ↔ (t ≤ (τ + 1) / c) := by
      intro t τ
      rw [le_div_iff₀ hc0]
      constructor <;> intro hh <;> linarith
    have hF : ∀ t τ, F t τ = (t * (1 - t))⁻¹ * (H τ / τ) * (if c * t - 1 ≤ τ then 1 else 0) := by
      intro t τ
      by_cases hh : c * t - 1 ≤ τ
      · rw [show F t τ = _ from indicator_of_mem (show (t, τ) ∈ S from hh) _]; simp [hh]
      · rw [show F t τ = _ from indicator_of_notMem (show (t, τ) ∉ S from hh) _]; simp [hh]
    have step1 : ∀ t ∈ uIcc a b, G (c * t) * (t * (1 - t))⁻¹ = ∫ τ in (1 : ℝ)..3, F t τ := by
      intro t ht
      rw [uIcc_of_le hab'] at ht
      simp only [hF]
      have e : (fun τ => (t * (1 - t))⁻¹ * (H τ / τ) * (if c * t - 1 ≤ τ then 1 else 0)) =
          fun τ => (t * (1 - t))⁻¹ * ((H τ / τ) * (if c * t - 1 ≤ τ then 1 else 0)) := by
        funext τ; ring
      rw [e, intervalIntegral.integral_const_mul,
        integral_ind_ge (by linarith [(hct t ht).1]) (by linarith [(hct t ht).2]) hKint]
      simp only [hGdef]
      ring
    have hint : Integrable (Function.uncurry F)
        ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (1 : ℝ) 3))) := by
      have hf : Integrable (fun t : ℝ => (t * (1 - t))⁻¹) (volume.restrict (Ioc a b)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hab').1 iW
      have hg : Integrable (fun t : ℝ => H t / t) (volume.restrict (Ioc (1 : ℝ) 3)) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hKint
      exact (hf.mul_prod hg).indicator
        (measurableSet_le ((measurable_const.mul measurable_fst).sub_const 1) measurable_snd)
    rw [intervalIntegral.integral_congr step1, swap13 hab' hint]
    apply intervalIntegral.integral_congr
    intro τ _
    show (∫ t in a..b, F t τ) = H τ / τ * Inner τ
    simp only [hF, hInner]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hiff t τ]
    ring
  -- the values of `Inner`
  have hInnerVal : ∀ τ ∈ Icc (1 : ℝ) 3, τ ≠ b * c - 1 →
      H τ / τ * Inner τ = L * (H τ * (ind (b * c - 1) 3 τ / τ)) +
        H τ * (ind (a * c - 1) (b * c - 1) τ / τ * log ((1 - a) * (τ + 1) / (a * (c - 1 - τ)))) := by
    intro τ hτ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h2 : ¬ (b * c - 1 ≤ τ ∧ τ ≤ 3) := fun hh => by linarith [hh.1]
      by_cases hlo : a * c - 1 ≤ τ
      · have hx1 : a ≤ (τ + 1) / c := by rw [le_div_iff₀ hc0]; linarith
        have hx2 : (τ + 1) / c < b := by rw [div_lt_iff₀ hc0]; linarith
        have hval : Inner τ = log ((1 - a) * (τ + 1) / (a * (c - 1 - τ))) := by
          simp only [hInner]
          rw [integral_ind_le (f := fun t : ℝ => (t * (1 - t))⁻¹) hx1 hx2.le,
            w_integral ha hx1 (hx2.trans hb)]
          congr 1
          have hcne : c - 1 - τ ≠ 0 := by
            have : b * c < c := by nlinarith
            linarith
          have hnum : (τ + 1) / c - a * ((τ + 1) / c) = (1 - a) * (τ + 1) / c := by ring
          have hden : a - a * ((τ + 1) / c) = a * (c - 1 - τ) / c := by
            field_simp
            ring
          rw [hnum, hden, div_div_div_cancel_right₀ hc0.ne']
        have h1 : a * c - 1 ≤ τ ∧ τ ≤ b * c - 1 := ⟨hlo, hlt.le⟩
        rw [hval]
        simp only [ind, if_neg h2, if_pos h1]
        ring
      · have hval : Inner τ = 0 := by
          simp only [hInner]
          apply intervalIntegral.integral_zero_ae
          filter_upwards with t ht
          rw [uIoc_of_le hab'] at ht
          have : ¬ t ≤ (τ + 1) / c := by
            rw [le_div_iff₀ hc0]
            intro hh
            have : a * c < t * c := by nlinarith [ht.1]
            linarith
          simp [this]
        have h1 : ¬ (a * c - 1 ≤ τ ∧ τ ≤ b * c - 1) := fun hh => hlo hh.1
        rw [hval]
        simp only [ind, if_neg h2, if_neg h1]
        ring
    · have h2 : b * c - 1 ≤ τ ∧ τ ≤ 3 := ⟨hgt.le, hτ.2⟩
      have h1 : ¬ (a * c - 1 ≤ τ ∧ τ ≤ b * c - 1) := fun hh => by linarith [hh.2]
      have hval : Inner τ = L := by
        simp only [hInner]
        rw [← hLeq]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab'] at ht
        have : t ≤ (τ + 1) / c := by
          rw [le_div_iff₀ hc0]
          nlinarith [ht.2]
        simp [this]
      rw [hval]
      simp only [ind, if_pos h2, if_neg h1]
      ring
  -- assembling
  have iS : IntervalIntegrable (fun t => H t * (sigma0 t / t)) volume 1 3 := by
    apply Burst4Split.product_integrable hH13
    have := sigma_term_integrable 1 1 one_pos
    simpa only [one_mul, mul_one] using this
  have iA : IntervalIntegrable (fun t => H t * (ind (b * c - 1) 3 t / t)) volume 1 3 :=
    Burst4Split.product_integrable hH13 (ind_integrable (by fun_prop)
      (fun t ht => (show (0 : ℝ) < t by linarith [ht.2.1]).ne'))
  have iB : IntervalIntegrable (fun t => H t * (ind (a * c - 1) (b * c - 1) t / t *
      log ((1 - a) * (t + 1) / (a * (c - 1 - t))))) volume 1 3 := by
    apply Burst4Split.product_integrable hH13
    apply ind_log_integrable (by fun_prop)
      (fun t ht => (show (0 : ℝ) < t by linarith [ht.2.1]).ne')
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      have : b * c < c := by nlinarith
      exact (mul_pos ha (by linarith [ht.1.2])).ne'
    · intro t ht
      have : b * c < c := by nlinarith
      exact (div_pos (mul_pos (by linarith) (by linarith [ht.2.1]))
        (mul_pos ha (by linarith [ht.1.2]))).ne'
  have hsplit : (∫ t in (1 : ℝ)..3, H t * ((sigma0 t + ind (b * c - 1) 3 t) / t)) =
      (∫ t in (1 : ℝ)..3, H t * (sigma0 t / t)) +
        ∫ t in (1 : ℝ)..3, H t * (ind (b * c - 1) 3 t / t) := by
    rw [← intervalIntegral.integral_add iS iA]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    ring
  have hnull : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ b * c - 1 := by
    simpa using (measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := b * c - 1)))
  have hae : (∫ τ in (1 : ℝ)..3, H τ / τ * Inner τ) =
      L * (∫ t in (1 : ℝ)..3, H t * (ind (b * c - 1) 3 t / t)) +
        ∫ t in (1 : ℝ)..3, H t * (ind (a * c - 1) (b * c - 1) t / t *
          log ((1 - a) * (t + 1) / (a * (c - 1 - t)))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (iA.const_mul L) iB]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hnull] with τ hne hτ
    rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hτ
    exact hInnerVal τ ⟨hτ.1.le, hτ.2⟩ hne
  have h61 := mul_le_mul_of_nonneg_left (eq61 hI) hL0
  have eR : (fun t => h (c * t) / (t * (1 - t))) = fun t => h (c * t) * (t * (1 - t))⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [eR, hsplit]
  rw [C2, C4, hae] at C1
  nlinarith

/-- The inputs of Lemma 6.1 hold for small `δ`. CONDITIONAL ON Propositions 1 and 2, through
their sub-leaves. -/
theorem l61_inputs {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → L61Inputs H h := by
  obtain ⟨d1, hd1, h1⟩ := proposition1 hF
  obtain ⟨d2, hd2, hA⟩ := corollary1 hF
  obtain ⟨d3, hd3, hpH⟩ := proposition2_H hF
  obtain ⟨d4, hd4, hph⟩ := proposition2_h hF
  refine ⟨min (min d1 d2) (min d3 d4), lt_min (lt_min hd1 hd2) (lt_min hd3 hd4),
    fun δ hδ hδ' H h hR => ?_⟩
  have e1 : δ < d1 := hδ'.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : δ < d2 := hδ'.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : δ < d3 := hδ'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : δ < d4 := hδ'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨fun s hs => (h1 δ hδ e1 H h hR s hs).1, fun s hs => (h1 δ hδ e1 H h hR s hs).2,
    hA δ hδ e2 H h hR, hpH δ hδ e3 H h hR, hph δ hδ e4 H h hR⟩

/-! ### Part D. Proposition 3, page 14, display 3.21, proved on page 29 -/


/-- SUB-LEAF of `proposition3`. Wu 2004 Lemma 5.1, page 22, proved on pages 22 to 25 from the
weighted inequality Lemma 4.1, page 15, and the estimates 5.1, 5.2 and 5.9 with 5.10:
`H(s) ≥ Ψ₁(s) + ½ ∫_{1−1/s}^{1−1/s'} h(s't) / (t(1−t)) dt + H(s')`
for `5 ≥ s' ≥ 3 ≥ s ≥ 2` and `s' − s'/s ≥ 2`. Cited. -/
theorem lemma51 {F f ω : ℝ → ℝ} (hF : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ s sp : ℝ, Admissible3 s sp →
        Psi1 ω s sp + 1 / 2 * (∫ t in (1 - 1 / s)..(1 - 1 / sp), h (sp * t) / (t * (1 - t))) +
          H sp ≤ H s := by
  sorry

/-- Wu 2004 Lemma 6.1, display 6.2, page 28, PROVED here as Wu does from
Proposition 2 through 6.4 and 6.1, see `eq64`, `eq61`, `eq62`: for `3 ≤ s' ≤ 5`,
`H(s') ≥ ∫₁³ H(t) {σ₀(t)/t · log(4/(s'−1)) + 1_{[s'−2,3]}(t)/t · log((t+1)/(s'−1))} dt`. -/
theorem lemma61_eq2 {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ sp : ℝ, 3 ≤ sp → sp ≤ 5 →
        (∫ t in (1 : ℝ)..3, H t * (sigma0 t / t * log (4 / (sp - 1)) +
          ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1)))) ≤ H sp := by
  obtain ⟨δ₀, hδ₀, hI⟩ := l61_inputs hF
  exact ⟨δ₀, hδ₀, fun δ hδ hδ' H h hR sp h3 h5 => eq62 (hI δ hδ hδ' H h hR) h3 h5⟩

/-- Wu 2004 Lemma 6.1, display 6.3, page 28, PROVED here as Wu does from
Proposition 2 and 6.1, see `eq63`: for `0 < a < b < 1` and `2 ≤ ac < bc ≤ 4`,
`∫_a^b h(ct)/(t(1−t)) dt ≥ log((b−ab)/(a−ab)) ∫₁³ H(t) (σ₀(t) + 1_{[bc−1,3]}(t))/t dt
  + ∫₁³ H(t) 1_{[ac−1,bc−1]}(t)/t · log((1−a)(t+1)/(a(c−1−t))) dt`. -/
theorem lemma61_eq3 {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ a b c : ℝ, 0 < a → a < b → b < 1 →
        2 ≤ a * c → a * c < b * c → b * c ≤ 4 →
        log ((b - a * b) / (a - a * b)) *
            (∫ t in (1 : ℝ)..3, H t * ((sigma0 t + ind (b * c - 1) 3 t) / t)) +
          (∫ t in (1 : ℝ)..3, H t * (ind (a * c - 1) (b * c - 1) t / t *
            log ((1 - a) * (t + 1) / (a * (c - 1 - t))))) ≤
          ∫ t in a..b, h (c * t) / (t * (1 - t)) := by
  obtain ⟨δ₀, hδ₀, hI⟩ := l61_inputs hF
  exact ⟨δ₀, hδ₀, fun δ hδ hδ' H h hR a b c ha hab hb hac habc hbc =>
    eq63 (hI δ hδ hδ' H h hR) ha hab hb hac habc hbc⟩

/-- The "simple calculation" of page 29 behind Proposition 3, pointwise: with
`L = log((s'−1)/(s−1))`, `Ξ₁(t; s) = K₂(t) + ½ (L K₃ₐ(t) + K₃ᵦ(t))`, where `K₂` is the kernel of
display 6.2 and `K₃ₐ`, `K₃ᵦ` are those of display 6.3 at `a = 1 − 1/s`, `b = 1 − 1/s'`,
`c = s'`. -/
theorem Xi1_split {s sp t : ℝ} (hs : 2 ≤ s) (hsp : 3 ≤ sp) :
    Xi1 s sp t = (sigma0 t / t * log (4 / (sp - 1)) +
        ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1))) +
      1 / 2 * (log ((sp - 1) / (s - 1)) * ((sigma0 t + ind (sp - 2) 3 t) / t) +
        ind (sp - sp / s - 1) (sp - 2) t / t * log ((t + 1) / ((s - 1) * (sp - 1 - t)))) := by
  have hs1 : (s - 1) ≠ 0 := by linarith
  have hsp1 : (sp - 1) ≠ 0 := by linarith
  have e1 : log (16 / ((s - 1) * (sp - 1))) =
      2 * log (4 / (sp - 1)) + log ((sp - 1) / (s - 1)) := by
    rw [log_div (by norm_num) (mul_ne_zero hs1 hsp1), log_mul hs1 hsp1,
      log_div (by norm_num) hsp1, log_div hsp1 hs1,
      show (16 : ℝ) = 4 ^ 2 by norm_num, log_pow]
    push_cast; ring
  unfold Xi1
  rw [e1]
  by_cases h2 : sp - 2 ≤ t ∧ t ≤ 3
  · have ht1 : (t + 1) ≠ 0 := by linarith [h2.1]
    have e2 : log ((t + 1) ^ 2 / ((s - 1) * (sp - 1))) =
        2 * log ((t + 1) / (sp - 1)) + log ((sp - 1) / (s - 1)) := by
      rw [log_div (pow_ne_zero 2 ht1) (mul_ne_zero hs1 hsp1), log_mul hs1 hsp1,
        log_div ht1 hsp1, log_div hsp1 hs1, log_pow]
      push_cast; ring
    rw [e2]
    simp only [ind, if_pos h2]
    ring
  · simp only [ind, if_neg h2]
    ring

/-- Display 6.3 at `a = 1 − 1/s`, `b = 1 − 1/s'`, `c = s'`, in the simplified form used on
page 29, including the degenerate case `s = s' = 3` where both sides vanish.
CONDITIONAL ON `lemma61_eq3`. -/
theorem lemma61_eq3_inst {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ s sp : ℝ, Admissible3 s sp →
        log ((sp - 1) / (s - 1)) *
            (∫ t in (1 : ℝ)..3, H t * ((sigma0 t + ind (sp - 2) 3 t) / t)) +
          (∫ t in (1 : ℝ)..3, H t * (ind (sp - sp / s - 1) (sp - 2) t / t *
            log ((t + 1) / ((s - 1) * (sp - 1 - t))))) ≤
          ∫ t in (1 - 1 / s)..(1 - 1 / sp), h (sp * t) / (t * (1 - t)) := by
  obtain ⟨δ₀, hδ₀, h63⟩ := lemma61_eq3 hF
  refine ⟨δ₀, hδ₀, fun δ hδ hδ' H h hR s sp hp => ?_⟩
  obtain ⟨hs2, hs3, hsp3, hsp5, hss⟩ := hp
  have hs0 : 0 < s := by linarith
  have hsp0 : 0 < sp := by linarith
  rcases lt_or_eq_of_le (hs3.trans hsp3) with hlt | heq
  · have ha : 0 < 1 - 1 / s := by
      have : 1 / s ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hs2
      linarith
    have hab : 1 - 1 / s < 1 - 1 / sp := by
      have : 1 / sp < 1 / s := one_div_lt_one_div_of_lt hs0 hlt
      linarith
    have hb : 1 - 1 / sp < 1 := by have : 0 < 1 / sp := by positivity
                                   linarith
    have eac : (1 - 1 / s) * sp = sp - sp / s := by field_simp
    have ebc : (1 - 1 / sp) * sp = sp - 1 := by field_simp
    have hh := h63 δ hδ hδ' H h hR (1 - 1 / s) (1 - 1 / sp) sp ha hab hb
      (by rw [eac]; exact hss) (mul_lt_mul_of_pos_right hab hsp0) (by rw [ebc]; linarith)
    have eL : ((1 - 1 / sp) - (1 - 1 / s) * (1 - 1 / sp)) /
        ((1 - 1 / s) - (1 - 1 / s) * (1 - 1 / sp)) = (sp - 1) / (s - 1) := by
      have : s - 1 ≠ 0 := by linarith
      have : sp - 1 ≠ 0 := by linarith
      field_simp
      ring
    have eG : ∀ t : ℝ, (1 - (1 - 1 / s)) * (t + 1) / ((1 - 1 / s) * (sp - 1 - t)) =
        (t + 1) / ((s - 1) * (sp - 1 - t)) := by
      intro t
      by_cases h0 : sp - 1 - t = 0
      · simp [h0]
      · have : s - 1 ≠ 0 := by linarith
        field_simp
        ring
    rw [eL, eac, ebc, show sp - 1 - 1 = sp - 2 by ring] at hh
    simp only [eG] at hh
    exact hh
  · -- the degenerate case `s = s' = 3`, where `a = b` and both sides are zero
    have hs : s = 3 := le_antisymm hs3 (heq ▸ hsp3)
    have hsp : sp = 3 := heq ▸ hs
    subst hs hsp
    have hz : ∀ t : ℝ, H t * (ind (3 - 3 / 3 - 1) (3 - 2) t / t *
        log ((t + 1) / ((3 - 1) * (3 - 1 - t)))) = 0 := by
      intro t
      by_cases hi : 3 - 3 / 3 - 1 ≤ t ∧ t ≤ 3 - 2
      · have ht : t = 1 := by norm_num at hi; linarith [hi.1, hi.2]
        subst ht; norm_num
      · simp only [ind, if_neg hi, zero_div, zero_mul, mul_zero]
    simp only [hz, intervalIntegral.integral_zero, intervalIntegral.integral_same]
    norm_num

/-- **Leaf `proposition3` from its split.** Wu 2004 Proposition 3, page 14, display 3.21, by the
proof on page 29: Lemma 5.1 together with displays 6.2 and 6.3 of Lemma 6.1. Same statement as
`Burst4Split.proposition3`. CONDITIONAL ON `lemma51`, and on Propositions 1 and 2 through
`lemma61_eq2`, `lemma61_eq3` and `corollary1`, which are PROVED from them in this file. -/
theorem proposition3 {F f ω : ℝ → ℝ} (hF : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → Proposition3 H ω := by
  obtain ⟨d1, hd1, h51⟩ := lemma51 hF hω
  obtain ⟨d2, hd2, h62⟩ := lemma61_eq2 hF
  obtain ⟨d3, hd3, h63⟩ := lemma61_eq3_inst hF
  obtain ⟨d4, hd4, hA⟩ := corollary1 hF
  refine ⟨min (min d1 d2) (min d3 d4), lt_min (lt_min hd1 hd2) (lt_min hd3 hd4),
    fun δ hδ hδ' H h hR s sp hp => ?_⟩
  have e1 : δ < d1 := hδ'.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : δ < d2 := hδ'.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : δ < d3 := hδ'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : δ < d4 := hδ'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hdec : AntitoneOn H (Icc (1 : ℝ) 3) :=
    (hA δ hδ e4 H h hR).mono (Icc_subset_Icc le_rfl (by norm_num))
  obtain ⟨hs2, hs3, hsp3, hsp5, hss⟩ := hp
  have i2 := Burst4Split.product_integrable hdec (kernel62_integrable hsp3)
  have i3a := Burst4Split.product_integrable hdec (kernel63a_integrable (sp - 2))
  have i3b := Burst4Split.product_integrable hdec (kernel63b_integrable (sp := sp) hs2)
  have q51 := h51 δ hδ e1 H h hR s sp ⟨hs2, hs3, hsp3, hsp5, hss⟩
  have q62 := h62 δ hδ e2 H h hR sp hsp3 hsp5
  have q63 := h63 δ hδ e3 H h hR s sp ⟨hs2, hs3, hsp3, hsp5, hss⟩
  set L := log ((sp - 1) / (s - 1))
  have hsplit : (∫ t in (1 : ℝ)..3, H t * Xi1 s sp t) =
      (∫ t in (1 : ℝ)..3, H t * (sigma0 t / t * log (4 / (sp - 1)) +
          ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1)))) +
        1 / 2 * (L * (∫ t in (1 : ℝ)..3, H t * ((sigma0 t + ind (sp - 2) 3 t) / t)) +
          (∫ t in (1 : ℝ)..3, H t * (ind (sp - sp / s - 1) (sp - 2) t / t *
            log ((t + 1) / ((s - 1) * (sp - 1 - t)))))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (i3a.const_mul L) i3b,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i2]
    · apply intervalIntegral.integral_congr
      intro t _
      simp only
      rw [Xi1_split hs2 hsp3]
      ring
    · exact ((i3a.const_mul L).add i3b).const_mul _
  rw [hsplit]
  linarith

/-! ### Part E. Proposition 4, page 15, display 3.22, proved on pages 29 and 30 -/

/-- The kernel of display 6.2, page 28. -/
def kernel62 (sp t : ℝ) : ℝ :=
  sigma0 t / t * log (4 / (sp - 1)) + ind (sp - 2) 3 t / t * log ((t + 1) / (sp - 1))

/-- The first kernel of display 6.3, page 28, at `b c = s'`, so that `bc − 1 = s' − 2`. -/
def kernel63a (sp t : ℝ) : ℝ := (sigma0 t + ind (sp - 2) 3 t) / t

/-- The second kernel of display 6.3, page 28, at `a = 1 − 1/x`, `b = 1 − 1/s'`, `c = s'`. -/
def kernel63b (x sp t : ℝ) : ℝ :=
  ind (sp - sp / x - 1) (sp - 2) t / t * log ((t + 1) / ((x - 1) * (sp - 1 - t)))

/-- The kernel on the right of display 6.6, page 29. -/
def L66 (p : Params) (t : ℝ) : ℝ :=
  ind (alpha p 5) (alpha p 3) t / (t * (1 - t / p.sp)) *
      log (p.sp / (p.k2 * p.sp - p.sp - p.k2 * t)) +
    ind (alpha p 3) (alpha p 1) t / (t * (1 - t / p.sp)) * log (p.sp - 1 - t)

/-- `L₁(t)` of display 6.7, page 29. -/
def L1 (p : Params) (t : ℝ) : ℝ :=
  ind (alpha p 6) (alpha p 4) t / (t * (1 - t / p.sp)) * log (p.sp ^ 2 /
      ((p.k1 * p.sp - p.sp - p.k1 * t) * (p.k3 * p.sp - p.sp - p.k3 * t))) +
    ind (alpha p 4) (alpha p 7) t / (t * (1 - t / p.sp)) *
      log (p.sp * (p.sp - 1 - t) / (p.k1 * p.sp - p.sp - p.k1 * t)) +
    ind (alpha p 7) (alpha p 3) t / (t * (1 - t / p.sp)) *
      log ((p.sp - 1 - t) * (p.k2 * p.sp - p.sp - p.k2 * t) / p.sp)

/-- `L₂(t)` of display 6.8, pages 29 and 30. -/
def L2 (p : Params) (t : ℝ) : ℝ :=
  ind (alpha p 8) (alpha p 0) t / t * log ((t + 1) / ((p.k2 - 1) * (p.k1 - 1 - t))) +
    ind (alpha p 0) (alpha p 3) t / t * log ((t + 1) / (p.k2 - 1)) +
    ind (alpha p 3) (alpha p 1) t / t * log (p.sp - 1 - t)

/-- The first double integral of Lemma 5.2, page 25. -/
def D1 (H : ℝ → ℝ) (p : Params) : ℝ :=
  ∫ t in (1 / p.sp)..(1 / p.k2), 1 / t *
    ∫ u in t..(1 / p.k2), H (p.sp - p.sp * t - p.sp * u) / (u * (1 - t - u))

/-- The second double integral of Lemma 5.2, page 25. -/
def D2 (H : ℝ → ℝ) (p : Params) : ℝ :=
  ∫ t in (1 / p.sp)..(1 / p.k1), 1 / t *
    ∫ u in (1 / p.k2)..(1 / p.k3), H (p.sp - p.sp * t - p.sp * u) / (u * (1 - t - u))

/-- The third double integral of Lemma 5.2, page 25. -/
def D3 (H : ℝ → ℝ) (p : Params) : ℝ :=
  ∫ t in (1 / p.sp)..(1 / p.k1), 1 / t *
    ∫ u in t..(1 / p.k2), H ((1 - t - u) / t) / (u * (1 - t - u))

/-! #### Display 6.8, page 29 -/

/-- `∫_α^β 1_{[lo,hi]} f = ∫_lo^hi f` for `α ≤ lo ≤ hi ≤ β`. -/
theorem integral_indicator_Icc {f : ℝ → ℝ} {α β lo hi : ℝ} (h1 : α ≤ lo) (h2 : lo ≤ hi)
    (h3 : hi ≤ β) :
    (∫ x in α..β, (Icc lo hi).indicator f x) = ∫ x in lo..hi, f x := by
  rw [intervalIntegral.integral_of_le (h1.trans (h2.trans h3)), intervalIntegral.integral_of_le h2,
    setIntegral_indicator measurableSet_Icc]
  apply setIntegral_congr_set
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (t := {lo}) _ Real.volume_singleton
    intro x hx
    simp only [mem_diff, mem_inter_iff, mem_Ioc, mem_Icc] at hx
    obtain ⟨⟨_, hlo, hhi⟩, hn⟩ := hx
    simp only [mem_singleton_iff]
    by_contra hne
    exact hn ⟨lt_of_le_of_ne hlo (Ne.symm hne), hhi⟩
  · rw [diff_eq_empty.2 (fun x (hx : x ∈ Ioc lo hi) =>
      (show x ∈ Ioc α β ∩ Icc lo hi from ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
        ⟨hx.1.le, hx.2⟩⟩))]
    exact measure_empty

/-- `∫_x^y dt/(t(1 − (1+v)t))` by its antiderivative `log t − log(1 − (1+v)t)`. -/
theorem wv_integral {v x y : ℝ} (hv : 0 < 1 + v) (hx : 0 < x) (hxy : x ≤ y)
    (hy : (1 + v) * y < 1) :
    (∫ t in x..y, (t * (1 - (1 + v) * t))⁻¹) =
      (log y - log (1 - (1 + v) * y)) - (log x - log (1 - (1 + v) * x)) := by
  have hderiv : ∀ t ∈ uIcc x y,
      HasDerivAt (fun t => log t - log (1 - (1 + v) * t)) ((t * (1 - (1 + v) * t))⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hxy] at ht
    have ht0 : 0 < t := hx.trans_le ht.1
    have ht1 : 0 < 1 - (1 + v) * t := by nlinarith [ht.2]
    have h1 := Real.hasDerivAt_log ht0.ne'
    have h2 := (((hasDerivAt_id t).const_mul (1 + v)).const_sub 1).log
      (by simp only [id]; exact ht1.ne')
    have ht0' := ht0.ne'
    have ht1' : 1 - t - t * v ≠ 0 := by
      intro h0; apply ht1.ne'; linarith
    convert h1.sub h2 using 1
    · funext y; simp
    · simp only [id]
      rw [show 1 - (1 + v) * t = 1 - t - t * v by ring]
      field_simp
      ring
  have hint : IntervalIntegrable (fun t => (t * (1 - (1 + v) * t))⁻¹) volume x y := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    rw [uIcc_of_le hxy] at ht
    exact (mul_pos (hx.trans_le ht.1) (by nlinarith [ht.2])).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- SUB-LEAF of `proposition4`. Wu 2004 Lemma 5.2, page 25, proved on pages 25 to 28 from the
new weighted inequality Lemma 4.2, page 17, with 5.11 to 5.20: for `5 ≥ s' ≥ 3 ≥ s ≥ 2`,
`s' − s'/s ≥ 2` and `s ≤ κ₃ < κ₂ < κ₁ ≤ s'`,
`H(s) ≥ Ψ₂(s) + 4/5 H(s') + 1/5 H(κ₁) + 1/5 ∫_{1−1/s}^{1−1/s'} h(s't)/(t(1−t)) dt
  + 1/5 ∫_{1−1/κ₂}^{1−1/s'} … + 1/5 ∫_{1−1/κ₃}^{1−1/s'} … + 1/5 (D₁ + D₂ + D₃)`,
with the three double integrals `D1`, `D2`, `D3` as printed. Cited. -/
theorem lemma52 {F f ω : ℝ → ℝ} (hF : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → ∀ p : Params, Admissible3 p.s p.sp →
        p.s ≤ p.k3 → p.k3 < p.k2 → p.k2 < p.k1 → p.k1 ≤ p.sp →
        Psi2 ω p + 4 / 5 * H p.sp + 1 / 5 * H p.k1 +
          1 / 5 * (∫ t in (1 - 1 / p.s)..(1 - 1 / p.sp), h (p.sp * t) / (t * (1 - t))) +
          1 / 5 * (∫ t in (1 - 1 / p.k2)..(1 - 1 / p.sp), h (p.sp * t) / (t * (1 - t))) +
          1 / 5 * (∫ t in (1 - 1 / p.k3)..(1 - 1 / p.sp), h (p.sp * t) / (t * (1 - t))) +
          1 / 5 * D1 H p + 1 / 5 * D2 H p + 1 / 5 * D3 H p ≤ H p.s := by
  sorry




/-! #### Elementary facts on the parameter range of Proposition 4 -/

/-- Splitting a support interval at an interior point, away from that point. -/
theorem ind_split {a m b t : ℝ} (ham : a ≤ m) (hmb : m ≤ b) (ht : t ≠ m) :
    ind a b t = ind a m t + ind m b t := by
  unfold ind
  by_cases h1 : a ≤ t ∧ t ≤ m
  · have h2 : ¬ (m ≤ t ∧ t ≤ b) := fun h => ht (le_antisymm h1.2 h.1)
    rw [if_pos ⟨h1.1, h1.2.trans hmb⟩, if_pos h1, if_neg h2]; norm_num
  · by_cases h2 : m ≤ t ∧ t ≤ b
    · rw [if_pos ⟨ham.trans h2.1, h2.2⟩, if_neg h1, if_pos h2]; norm_num
    · have h3 : ¬ (a ≤ t ∧ t ≤ b) := by
        rintro ⟨ha, hb⟩
        rcases le_total t m with h | h
        · exact h1 ⟨ha, h⟩
        · exact h2 ⟨h, hb⟩
      rw [if_neg h3, if_neg h1, if_neg h2]; norm_num

/-- A summand supported on `[a, b]` only sees its factor on `[a, b]`. -/
theorem ind_mul_eq_all {a b t u v : ℝ} (h : a ≤ t → t ≤ b → u = v) :
    ∀ D : ℝ, ind a b t / D * u = ind a b t / D * v := by
  intro D
  by_cases hab : a ≤ t ∧ t ≤ b
  · rw [h hab.1 hab.2]
  · simp only [ind, if_neg hab, zero_div, zero_mul]

theorem alpha_vals (s sp k1 k2 k3 : ℝ) :
    alpha ⟨s, sp, k1, k2, k3⟩ 0 = k1 - 2 ∧ alpha ⟨s, sp, k1, k2, k3⟩ 1 = sp - 2 ∧
    alpha ⟨s, sp, k1, k2, k3⟩ 2 = sp - sp / s - 1 ∧
    alpha ⟨s, sp, k1, k2, k3⟩ 3 = sp - sp / k2 - 1 ∧
    alpha ⟨s, sp, k1, k2, k3⟩ 4 = sp - sp / k3 - 1 ∧
    alpha ⟨s, sp, k1, k2, k3⟩ 5 = sp - 2 * sp / k2 ∧
    alpha ⟨s, sp, k1, k2, k3⟩ 6 = sp - sp / k1 - sp / k3 ∧
    alpha ⟨s, sp, k1, k2, k3⟩ 7 = sp - sp / k1 - sp / k2 ∧
    alpha ⟨s, sp, k1, k2, k3⟩ 8 = k1 - k1 / k2 - 1 := by
  simp [alpha]

/-- The positivity facts behind the logarithms of displays 3.22 and 6.5 to 6.8, page 15 and
pages 29 and 30, on the parameter range of Proposition 4. -/
structure Adm4Facts (s sp k1 k2 k3 : ℝ) : Prop where
  s2 : 2 ≤ s
  sp3 : 3 ≤ sp
  sp5 : sp ≤ 5
  k1_3 : 3 ≤ k1
  k1sp : k1 ≤ sp
  sk3 : s ≤ k3
  k32 : k3 < k2
  k21 : k2 < k1
  ssp : 2 ≤ sp - sp / s
  a2_le : sp - 2 ≤ 3
  a1_lt_a4 : k1 - 2 < sp - sp / k2 - 1
  a4_one : 1 ≤ sp - sp / k2 - 1
  a5_one : 1 ≤ sp - sp / k3 - 1
  a8_le_a4 : sp - sp / k1 - sp / k2 ≤ sp - sp / k2 - 1
  a4_le_a2 : sp - sp / k2 - 1 ≤ sp - 2
  a6_le_a8 : sp - 2 * sp / k2 ≤ sp - sp / k1 - sp / k2
  X1_of_a5 : ∀ t, t ≤ sp - sp / k3 - 1 → 0 < k1 * sp - sp - k1 * t
  X1_of_a8 : ∀ t, t ≤ sp - sp / k1 - sp / k2 → 0 < k1 * sp - sp - k1 * t
  X2_of_a4 : ∀ t, t ≤ sp - sp / k2 - 1 → 0 < k2 * sp - sp - k2 * t
  X3_of_a5 : ∀ t, t ≤ sp - sp / k3 - 1 → 0 < k3 * sp - sp - k3 * t

theorem adm4_facts {s sp k1 k2 k3 : ℝ} (hp : Admissible4 ⟨s, sp, k1, k2, k3⟩) :
    Adm4Facts s sp k1 k2 k3 := by
  obtain ⟨⟨hs2, hs3, hsp3, hsp5, hss⟩, hk3, hk32, hk21, hk1, hal, h14, h58⟩ := hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := alpha_vals s sp k1 k2 k3
  dsimp only at hk3 hk32 hk21 hk1 hss hs2 hs3 hsp3 hsp5
  have a0 := hal 0
  have a1 := hal 1
  have a3 := hal 3
  have a4 := hal 4
  rw [e0] at a0
  rw [e1] at a1
  rw [e3] at a3
  rw [e4] at a4
  rw [e0, e3] at h14
  have hk3p : 0 < k3 := by linarith
  have hk2p : 0 < k2 := by linarith
  have hk1p : 0 < k1 := by linarith
  have hsp0 : 0 < sp := by linarith
  have c1 : k1 * (sp / k1) = sp := by field_simp
  have c2 : k2 * (sp / k2) = sp := by field_simp
  have c3 : k3 * (sp / k3) = sp := by field_simp
  have o1 : 1 ≤ sp / k1 := (one_le_div hk1p).2 hk1
  have o2 : 1 ≤ sp / k2 := (one_le_div hk2p).2 (by linarith)
  have o12 : sp / k1 ≤ sp / k2 := div_le_div_of_nonneg_left hsp0.le hk2p hk21.le
  refine ⟨hs2, hsp3, hsp5, by linarith [a0.1], hk1, hk3, hk32, hk21, hss, a1.2, h14, a3.1, a4.1,
    by linarith, by linarith, by linarith [show 2 * sp / k2 = sp / k2 + sp / k2 by ring], ?_, ?_, ?_, ?_⟩
  · intro t ht
    have h1 := mul_le_mul_of_nonneg_left ht hk1p.le
    have h2 : k3 * (sp / k3) < k1 * (sp / k3) :=
      mul_lt_mul_of_pos_right (hk32.trans hk21) (div_pos hsp0 hk3p)
    rw [c3] at h2
    rw [show k1 * (sp - sp / k3 - 1) = k1 * sp - k1 * (sp / k3) - k1 by ring] at h1
    linarith
  · intro t ht
    have h1 := mul_le_mul_of_nonneg_left ht hk1p.le
    rw [show k1 * (sp - sp / k1 - sp / k2) = k1 * sp - k1 * (sp / k1) - k1 * (sp / k2) by ring,
      c1] at h1
    have : 0 < k1 * (sp / k2) := mul_pos hk1p (div_pos hsp0 hk2p)
    linarith
  · intro t ht
    have h1 := mul_le_mul_of_nonneg_left ht hk2p.le
    rw [show k2 * (sp - sp / k2 - 1) = k2 * sp - k2 * (sp / k2) - k2 by ring, c2] at h1
    linarith
  · intro t ht
    have h1 := mul_le_mul_of_nonneg_left ht hk3p.le
    rw [show k3 * (sp - sp / k3 - 1) = k3 * sp - k3 * (sp / k3) - k3 by ring, c3] at h1
    linarith

theorem F_one_div {k v : ℝ} (hk : 0 < k) (h : 0 < k - 1 - v) :
    log (1 / k) - log (1 - (1 + v) * (1 / k)) = -log (k - 1 - v) := by
  rw [show 1 - (1 + v) * (1 / k) = (k - 1 - v) / k by field_simp; ring,
    log_div h.ne' hk.ne', one_div, Real.log_inv]
  ring

theorem F_T1 {k2 v : ℝ} (hk2 : 1 < k2) (hv : 0 < v + 1) :
    log ((1 - 1 / k2) / (v + 1)) - log (1 - (1 + v) * ((1 - 1 / k2) / (v + 1))) =
      log (k2 - 1) - log (v + 1) := by
  have hk0 : (0 : ℝ) < k2 := by linarith
  rw [show 1 - (1 + v) * ((1 - 1 / k2) / (v + 1)) = 1 / k2 by field_simp; ring,
    show (1 - 1 / k2) / (v + 1) = (k2 - 1) / (k2 * (v + 1)) by field_simp,
    log_div (by linarith) (mul_pos hk0 hv).ne', log_mul hk0.ne' hv.ne', one_div, Real.log_inv]
  ring

theorem F_T2 {v : ℝ} (hv : 0 < v + 2) :
    log (1 / (v + 2)) - log (1 - (1 + v) * (1 / (v + 2))) = 0 := by
  rw [show 1 - (1 + v) * (1 / (v + 2)) = 1 / (v + 2) by field_simp; ring]
  ring

/-- **Display 6.8 PROVED**, formerly a sub-leaf of `proposition4`. Wu 2004 pages 29 and 30: the change of variable `v = (1 − t − u)/t` and an
interchange of the order of integration give `D₃ = ∫₁³ H(t) L₂(t) dt`. -/
theorem eq68 {H : ℝ → ℝ} (hH : AntitoneOn H (Icc (1 : ℝ) 3)) {p : Params}
    (hp : Admissible4 p) : D3 H p = ∫ t in (1 : ℝ)..3, H t * L2 p t := by
  obtain ⟨s, sp, k1, k2, k3⟩ := p
  have hF := adm4_facts hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := alpha_vals s sp k1 k2 k3
  have a8 : 1 ≤ k1 - k1 / k2 - 1 := by
    have := (hp.2.2.2.2.2.1 8).1; rwa [e8] at this
  have hk2 : 2 < k2 := by linarith [hF.s2, hF.sk3, hF.k32]
  have hk20 : 0 < k2 := by linarith
  have hk10 : 0 < k1 := by linarith [hF.k21]
  have hsp0 : 0 < sp := by linarith [hF.sp3]
  have hαβ : 1 / sp ≤ 1 / k1 := one_div_le_one_div_of_le hk10 hF.k1sp
  have hα0 : 0 < 1 / sp := by positivity
  have hKint := H_div_integrable hH
  -- orders of the alphas
  have o91 : k1 - k1 / k2 - 1 ≤ k1 - 2 := by
    have : 1 ≤ k1 / k2 := (one_le_div hk20).2 hF.k21.le
    linarith
  have o14 := hF.a1_lt_a4
  have o42 := hF.a4_le_a2
  unfold D3 L2
  simp only [e0, e1, e3, e8]
  -- the region and the integrand after the change of variable
  let R : Set (ℝ × ℝ) := {z | (1 - 1 / k2) / (z.2 + 1) ≤ z.1 ∧ z.1 ≤ 1 / (z.2 + 2)}
  let G : ℝ × ℝ → ℝ := fun z => H z.2 / z.2 * (z.1 * (1 - (1 + z.2) * z.1))⁻¹
  let F : ℝ → ℝ → ℝ := fun t v => R.indicator G (t, v)
  -- step 1: the change of variable, for each `t`
  have step1 : ∀ t ∈ uIcc (1 / sp) (1 / k1),
      1 / t * (∫ u in t..(1 / k2), H ((1 - t - u) / t) / (u * (1 - t - u))) =
        ∫ v in (1 : ℝ)..3, F t v := by
    intro t ht
    rw [uIcc_of_le hαβ] at ht
    have ht0 : 0 < t := hα0.trans_le ht.1
    have ht1k : t * k1 ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ht.2 hk10.le
      rwa [one_div_mul_cancel hk10.ne'] at this
    have htsp : 1 ≤ t * sp := by
      have := mul_le_mul_of_nonneg_right ht.1 hsp0.le
      rwa [one_div_mul_cancel hsp0.ne'] at this
    set A := (1 - t - 1 / k2) / t with hA
    set B := (1 - 2 * t) / t with hB
    have hA1 : 1 ≤ A := by
      rw [hA, le_div_iff₀ ht0]
      have h1 : (1 - 1 / k2) * (t * k1) ≤ 1 - 1 / k2 := by
        have : 0 ≤ 1 - 1 / k2 := by
          have : 1 / k2 ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk2.le
          linarith
        nlinarith
      have h2 : (k1 - k1 / k2 - 1) * t = (1 - 1 / k2) * (t * k1) - t := by ring
      nlinarith
    have hB3 : B ≤ 3 := by
      rw [hB, div_le_iff₀ ht0]
      nlinarith [hF.a2_le]
    have hAB : A ≤ B := by
      rw [hA, hB]
      apply div_le_div_of_nonneg_right _ ht0.le
      have : t ≤ 1 / k2 := ht.2.trans (one_div_le_one_div_of_le hk20 hF.k21.le)
      linarith
    let f : ℝ → ℝ := fun u => H ((1 - t - u) / t) / (u * (1 - t - u))
    have hsub := intervalIntegral.integral_comp_mul_add (f := f) (a := A) (b := B)
      (neg_ne_zero.2 ht0.ne') (1 - t)
    have eA : -t * A + (1 - t) = 1 / k2 := by rw [hA]; field_simp; ring
    have eB : -t * B + (1 - t) = t := by rw [hB]; field_simp; ring
    rw [eA, eB, smul_eq_mul] at hsub
    have hsub' : (∫ u in t..(1 / k2), f u) = t * ∫ v in A..B, f (-t * v + (1 - t)) := by
      rw [intervalIntegral.integral_symm, hsub]
      field_simp
    have hval : ∀ v, f (-t * v + (1 - t)) = H v / v * (t * (1 - (1 + v) * t))⁻¹ := by
      intro v
      simp only [f]
      rw [show (1 - t - (-t * v + (1 - t))) / t = v by field_simp; ring,
        show (-t * v + (1 - t)) * (1 - t - (-t * v + (1 - t))) =
          (t * (1 - (1 + v) * t)) * v by ring,
        div_eq_mul_inv, mul_inv, div_eq_mul_inv]
      ring
    show 1 / t * (∫ u in t..(1 / k2), f u) = _
    rw [hsub', ← mul_assoc, one_div_mul_cancel ht0.ne', one_mul]
    simp only [hval]
    rw [← integral_indicator_Icc (f := fun v => H v / v * (t * (1 - (1 + v) * t))⁻¹)
      (α := 1) (β := 3) hA1 hAB hB3]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hv
    have hv1 : 0 < v + 1 := by linarith [hv.1]
    have hv2 : 0 < v + 2 := by linarith [hv.1]
    have hmem : v ∈ Icc A B ↔ (t, v) ∈ R := by
      simp only [mem_Icc, R, mem_setOf_eq]
      rw [hA, hB, div_le_iff₀ ht0, le_div_iff₀ ht0, div_le_iff₀ hv1, le_div_iff₀ hv2]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
    by_cases hm : v ∈ Icc A B
    · rw [indicator_of_mem hm]
      show _ = R.indicator G (t, v)
      rw [indicator_of_mem (hmem.1 hm)]
    · rw [indicator_of_notMem hm]
      show _ = R.indicator G (t, v)
      rw [indicator_of_notMem (fun h' => hm (hmem.2 h'))]
  -- step 2: integrability on the product
  have hR : MeasurableSet R := by
    apply MeasurableSet.inter
    · exact measurableSet_le (by fun_prop) measurable_fst
    · exact measurableSet_le measurable_fst (by fun_prop)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (1 / sp) (1 / k1))).prod (volume.restrict (Ioc (1 : ℝ) 3))) := by
    have hg2 : Integrable (fun v : ℝ => H v / v) (volume.restrict (Ioc (1 : ℝ) 3)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hKint
    have hbd : Integrable (fun z : ℝ × ℝ => sp ^ 2 * ‖H z.2 / z.2‖)
        ((volume.restrict (Ioc (1 / sp) (1 / k1))).prod (volume.restrict (Ioc (1 : ℝ) 3))) :=
      (integrable_const (sp ^ 2)).mul_prod hg2.norm
    refine hbd.mono' ?_ ?_
    · have hG : AEStronglyMeasurable G
          ((volume.restrict (Ioc (1 / sp) (1 / k1))).prod (volume.restrict (Ioc (1 : ℝ) 3))) :=
        hg2.aestronglyMeasurable.comp_snd.mul
          (Measurable.aestronglyMeasurable
            (f := fun z : ℝ × ℝ => (z.1 * (1 - (1 + z.2) * z.1))⁻¹) (by fun_prop))
      exact hG.indicator hR
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) ?_
      rintro ⟨t, v⟩ ⟨ht, hv⟩
      simp only [mem_Ioc] at ht hv
      show ‖R.indicator G (t, v)‖ ≤ sp ^ 2 * ‖H v / v‖
      by_cases hm : (t, v) ∈ R
      · rw [indicator_of_mem hm]
        simp only [G, norm_mul, norm_inv]
        have hm2 : t * (v + 2) ≤ 1 := by
          have := hm.2; rwa [le_div_iff₀ (by linarith)] at this
        have hq : 1 / sp ^ 2 ≤ t * (1 - (1 + v) * t) := by
          have h1 : 1 / sp ≤ t := ht.1.le
          have h2 : t ≤ 1 - (1 + v) * t := by nlinarith
          calc 1 / sp ^ 2 = 1 / sp * (1 / sp) := by ring
            _ ≤ t * (1 - (1 + v) * t) := mul_le_mul h1 (h1.trans h2) hα0.le (by linarith)
        have hq0 : 0 < t * (1 - (1 + v) * t) := lt_of_lt_of_le (by positivity) hq
        rw [← norm_mul, Real.norm_of_nonneg hq0.le, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [inv_le_comm₀ hq0 (by positivity)]
        simpa [one_div] using hq
      · rw [indicator_of_notMem hm, norm_zero]
        positivity
  -- step 3: interchange and inner integrals
  rw [intervalIntegral.integral_congr step1, swap13 hαβ hint]
  have hnull : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ ({k1 - k1 / k2 - 1, k1 - 2, sp - sp / k2 - 1,
      sp - 2} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite _).measure_zero _)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hnull] with v hne hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  obtain ⟨n9, n1, n4, n2⟩ := hne
  rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hv
  have hv1 : 0 < v + 1 := by linarith [hv.1]
  have hv2 : 0 < v + 2 := by linarith [hv.1]
  have hv0 : 0 < v := by linarith [hv.1]
  set T1 := (1 - 1 / k2) / (v + 1) with hT1
  set T2 := 1 / (v + 2) with hT2
  set w : ℝ → ℝ := fun t => (t * (1 - (1 + v) * t))⁻¹ with hw
  have hFv : ∀ t, F t v = H v / v * (Icc T1 T2).indicator w t := by
    intro t
    by_cases hm : t ∈ Icc T1 T2
    · rw [indicator_of_mem hm]
      show R.indicator G (t, v) = _
      rw [indicator_of_mem (show (t, v) ∈ R from hm)]
    · rw [indicator_of_notMem hm, mul_zero]
      show R.indicator G (t, v) = _
      rw [indicator_of_notMem (show (t, v) ∉ R from hm)]
  show (∫ t in (1 / sp)..(1 / k1), F t v) = H v * _
  simp only [hFv]
  rw [intervalIntegral.integral_const_mul]
  have hT10 : 0 < T1 := by
    rw [hT1]; apply div_pos _ hv1
    have : 1 / k2 < 1 := (div_lt_one hk20).2 (by linarith)
    linarith
  -- comparisons of `T1`, `T2` with the ends, in terms of `v`
  have cT1β : T1 ≤ 1 / k1 ↔ k1 - k1 / k2 - 1 ≤ v := by
    rw [hT1, div_le_div_iff₀ hv1 hk10, one_mul]
    constructor <;> intro h <;>
      nlinarith [show k1 * (1 / k2) = k1 / k2 by ring]
  have cT1α : 1 / sp ≤ T1 ↔ v ≤ sp - sp / k2 - 1 := by
    rw [hT1, div_le_div_iff₀ hsp0 hv1, one_mul]
    constructor <;> intro h <;>
      nlinarith [show sp * (1 / k2) = sp / k2 by ring]
  have cT2β : 1 / k1 ≤ T2 ↔ v ≤ k1 - 2 := by
    rw [hT2, div_le_div_iff₀ hk10 hv2, one_mul, one_mul]
    constructor <;> intro h <;> linarith
  have cT2α : 1 / sp ≤ T2 ↔ v ≤ sp - 2 := by
    rw [hT2, div_le_div_iff₀ hsp0 hv2, one_mul, one_mul]
    constructor <;> intro h <;> linarith
  have hlog1 : 0 < k2 - 1 := by linarith
  rcases lt_or_gt_of_ne n9 with h9 | h9
  · -- `v < α₉`: the slice is empty
    have hz : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        have hT : ¬ T1 ≤ 1 / k1 := fun h' => by linarith [cT1β.1 h']
        exact indicator_of_notMem (fun hm => hT (hm.1.trans ht.2)) _)]
      simp
    rw [hz]
    have i1 : ¬ (k1 - k1 / k2 - 1 ≤ v ∧ v ≤ k1 - 2) := fun h' => by linarith [h'.1]
    have i2 : ¬ (k1 - 2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by linarith [h'.1]
    have i3 : ¬ (sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2) := fun h' => by linarith [h'.1]
    simp only [ind, if_neg i1, if_neg i2, if_neg i3]
    ring
  rcases lt_or_gt_of_ne n1 with h1 | h1
  · -- `α₉ < v < α₁`
    have hT1β : T1 ≤ 1 / k1 := cT1β.2 h9.le
    have hT1α : 1 / sp ≤ T1 := cT1α.2 (by linarith)
    have hT2β : 1 / k1 ≤ T2 := cT2β.2 h1.le
    have hval : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) =
        -log (k1 - 1 - v) - (log (k2 - 1) - log (v + 1)) := by
      rw [intervalIntegral.integral_congr (g := (Icc T1 (1 / k1)).indicator w) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        by_cases hm : t ∈ Icc T1 (1 / k1)
        · rw [indicator_of_mem hm,
            indicator_of_mem (show t ∈ Icc T1 T2 from ⟨hm.1, hm.2.trans hT2β⟩)]
        · rw [indicator_of_notMem hm, indicator_of_notMem
            (fun (h' : t ∈ Icc T1 T2) => hm ⟨h'.1, ht.2⟩)]),
        integral_indicator_Icc hT1α hT1β le_rfl,
        wv_integral (by linarith : (0 : ℝ) < 1 + v) hT10 hT1β (by
          rw [mul_one_div, div_lt_one hk10]; linarith),
        F_one_div hk10 (by linarith), F_T1 (by linarith) hv1]
    rw [hval]
    have i1 : k1 - k1 / k2 - 1 ≤ v ∧ v ≤ k1 - 2 := ⟨h9.le, h1.le⟩
    have i2 : ¬ (k1 - 2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by linarith [h'.1]
    have i3 : ¬ (sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2) := fun h' => by linarith [h'.1]
    simp only [ind, if_pos i1, if_neg i2, if_neg i3]
    rw [log_div hv1.ne' (mul_pos hlog1 (by linarith)).ne', log_mul hlog1.ne' (by linarith)]
    field_simp
    ring
  rcases lt_or_gt_of_ne n4 with h4 | h4
  · -- `α₁ < v < α₄`
    have hT1α : 1 / sp ≤ T1 := cT1α.2 h4.le
    have hT2β : T2 ≤ 1 / k1 := by
      rw [hT2, div_le_div_iff₀ hv2 hk10, one_mul, one_mul]; linarith
    have hT12 : T1 ≤ T2 := by
      rw [hT1, hT2, div_le_div_iff₀ hv1 hv2, one_mul]
      have : (1 - 1 / k2) * (v + 2) ≤ v + 1 := by
        have hk : 1 ≤ (v + 2) / k2 := (one_le_div hk20).2 (by linarith [hF.k21])
        have : (1 - 1 / k2) * (v + 2) = v + 2 - (v + 2) / k2 := by ring
        linarith
      exact this
    have hval : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) =
        0 - (log (k2 - 1) - log (v + 1)) := by
      rw [integral_indicator_Icc hT1α hT12 hT2β,
        wv_integral (by linarith : (0 : ℝ) < 1 + v) hT10 hT12 (by rw [hT2, mul_one_div, div_lt_one hv2]; linarith),
        F_T2 hv2, F_T1 (by linarith) hv1]
    rw [hval]
    have i1 : ¬ (k1 - k1 / k2 - 1 ≤ v ∧ v ≤ k1 - 2) := fun h' => by linarith [h'.2]
    have i2 : k1 - 2 ≤ v ∧ v ≤ sp - sp / k2 - 1 := ⟨h1.le, h4.le⟩
    have i3 : ¬ (sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2) := fun h' => by linarith [h'.1]
    simp only [ind, if_neg i1, if_pos i2, if_neg i3]
    rw [log_div hv1.ne' hlog1.ne']
    field_simp
    ring
  rcases lt_or_gt_of_ne n2 with h2 | h2
  · -- `α₄ < v < α₂`
    have hT2α : 1 / sp ≤ T2 := cT2α.2 h2.le
    have hT2β : T2 ≤ 1 / k1 := by
      rw [hT2, div_le_div_iff₀ hv2 hk10, one_mul, one_mul]; linarith
    have hT1α : T1 < 1 / sp := by
      by_contra hc; exact absurd (cT1α.1 (not_lt.1 hc)) (by linarith)
    have hval : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) =
        0 - (-log (sp - 1 - v)) := by
      rw [intervalIntegral.integral_congr (g := (Icc (1 / sp) T2).indicator w) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        by_cases hm : t ∈ Icc (1 / sp) T2
        · rw [indicator_of_mem hm,
            indicator_of_mem (show t ∈ Icc T1 T2 from ⟨hT1α.le.trans hm.1, hm.2⟩)]
        · rw [indicator_of_notMem hm, indicator_of_notMem
            (fun (h' : t ∈ Icc T1 T2) => hm ⟨ht.1, h'.2⟩)]),
        integral_indicator_Icc le_rfl hT2α hT2β,
        wv_integral (by linarith : (0 : ℝ) < 1 + v) hα0 hT2α (by rw [hT2, mul_one_div, div_lt_one hv2]; linarith),
        F_T2 hv2, F_one_div hsp0 (by linarith)]
    rw [hval]
    have i1 : ¬ (k1 - k1 / k2 - 1 ≤ v ∧ v ≤ k1 - 2) := fun h' => by linarith [h'.2]
    have i2 : ¬ (k1 - 2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by linarith [h'.2]
    have i3 : sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2 := ⟨h4.le, h2.le⟩
    simp only [ind, if_neg i1, if_neg i2, if_pos i3]
    field_simp
    ring
  · -- `v > α₂`: the slice is empty
    have hz : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        have hT : ¬ 1 / sp ≤ T2 := fun h' => by linarith [cT2α.1 h']
        exact indicator_of_notMem (fun hm => hT (ht.1.trans hm.2)) _)]
      simp
    rw [hz]
    have i1 : ¬ (k1 - k1 / k2 - 1 ≤ v ∧ v ≤ k1 - 2) := fun h' => by linarith [h'.2]
    have i2 : ¬ (k1 - 2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by linarith [h'.2]
    have i3 : ¬ (sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2) := fun h' => by linarith [h'.2]
    simp only [ind, if_neg i1, if_neg i2, if_neg i3]
    ring

/-! #### Displays 6.6 and 6.7, page 29 -/

/-- `∫_x^y dt/(t(q − t)) = ((log y − log(q − y)) − (log x − log(q − x)))/q`. -/
theorem wq_integral {q x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < q) :
    (∫ t in x..y, (t * (q - t))⁻¹) =
      ((log y - log (q - y)) - (log x - log (q - x))) / q := by
  have hq : 0 < q := by linarith
  have hderiv : ∀ t ∈ uIcc x y,
      HasDerivAt (fun t => (log t - log (q - t)) / q) ((t * (q - t))⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hxy] at ht
    have ht0 : 0 < t := hx.trans_le ht.1
    have ht1 : 0 < q - t := by linarith [ht.2]
    have h1 := Real.hasDerivAt_log ht0.ne'
    have h2 := ((hasDerivAt_id t).const_sub q).log (by simp only [id]; exact ht1.ne')
    have ht0' := ht0.ne'
    have ht1' := ht1.ne'
    have hq' := hq.ne'
    convert (h1.sub h2).div_const q using 1
    · funext y; simp
    · simp only [id]
      field_simp
      ring
  have hint : IntervalIntegrable (fun t => (t * (q - t))⁻¹) volume x y := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    rw [uIcc_of_le hxy] at ht
    exact (mul_pos (hx.trans_le ht.1) (by linarith [ht.2])).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

theorem Fq_half {q : ℝ} : log (q / 2) - log (q - q / 2) = 0 := by
  rw [show q - q / 2 = q / 2 by ring]; ring

theorem Fq_sub {q k : ℝ} (hk : 0 < k) (h : 0 < k * q - 1) :
    log (q - 1 / k) - log (q - (q - 1 / k)) = log (k * q - 1) := by
  rw [show q - (q - 1 / k) = 1 / k by ring, show q - 1 / k = (k * q - 1) / k by field_simp,
    log_div h.ne' hk.ne', one_div, Real.log_inv]
  ring

theorem Fq_one_div {q k : ℝ} (hk : 0 < k) (h : 0 < k * q - 1) :
    log (1 / k) - log (q - 1 / k) = -log (k * q - 1) := by
  rw [show q - 1 / k = (k * q - 1) / k by field_simp, log_div h.ne' hk.ne', one_div,
    Real.log_inv]
  ring

/-- **Display 6.6 PROVED**, formerly a sub-leaf of `proposition4`. Wu 2004 page 29: the change of
variable `v = s'(1 − t − u)` and an interchange of the order of integration give
`D₁ = ∫₁³ H(t) L66(t) dt`. -/
theorem eq66 {H : ℝ → ℝ} (hH : AntitoneOn H (Icc (1 : ℝ) 3)) {p : Params}
    (hp : Admissible4 p) : D1 H p = ∫ t in (1 : ℝ)..3, H t * L66 p t := by
  obtain ⟨s, sp, k1, k2, k3⟩ := p
  have hF := adm4_facts hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := alpha_vals s sp k1 k2 k3
  have a5 : 1 ≤ sp - 2 * sp / k2 := by
    have := (hp.2.2.2.2.2.1 5).1; rwa [e5] at this
  have hk2 : 2 < k2 := by linarith [hF.s2, hF.sk3, hF.k32]
  have hk20 : 0 < k2 := by linarith
  have hsp0 : 0 < sp := by linarith [hF.sp3]
  have hk2sp : k2 ≤ sp := by linarith [hF.k21, hF.k1sp]
  have hαβ : 1 / sp ≤ 1 / k2 := one_div_le_one_div_of_le hk20 hk2sp
  have hα0 : 0 < 1 / sp := by positivity
  have hKint := H_div_integrable hH
  have o42 := hF.a4_le_a2
  have o64 : sp - 2 * sp / k2 ≤ sp - sp / k2 - 1 := by
    have := hF.a6_le_a8; have := hF.a8_le_a4; linarith
  unfold D1 L66
  simp only [e1, e3, e5]
  let R : Set (ℝ × ℝ) := {z | 1 - z.2 / sp - 1 / k2 ≤ z.1 ∧ z.1 ≤ (1 - z.2 / sp) / 2}
  let G : ℝ × ℝ → ℝ := fun z => H z.2 / z.2 * (z.1 * ((1 - z.2 / sp) - z.1))⁻¹
  let F : ℝ → ℝ → ℝ := fun t v => R.indicator G (t, v)
  have step1 : ∀ t ∈ uIcc (1 / sp) (1 / k2),
      1 / t * (∫ u in t..(1 / k2), H (sp - sp * t - sp * u) / (u * (1 - t - u))) =
        ∫ v in (1 : ℝ)..3, F t v := by
    intro t ht
    rw [uIcc_of_le hαβ] at ht
    have ht0 : 0 < t := hα0.trans_le ht.1
    have htk : t * k2 ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ht.2 hk20.le
      rwa [one_div_mul_cancel hk20.ne'] at this
    have htsp : 1 ≤ t * sp := by
      have := mul_le_mul_of_nonneg_right ht.1 hsp0.le
      rwa [one_div_mul_cancel hsp0.ne'] at this
    set A := sp * (1 - t - 1 / k2) with hA
    set B := sp * (1 - 2 * t) with hB
    have hk2' : sp * (1 / k2) = sp / k2 := by ring
    have hA1 : 1 ≤ A := by
      have h1 : sp * t ≤ sp * (1 / k2) := mul_le_mul_of_nonneg_left ht.2 hsp0.le
      have h2 : 2 * sp / k2 = 2 * (sp * (1 / k2)) := by ring
      have h3 : sp * (1 - t - 1 / k2) = sp - sp * t - sp * (1 / k2) := by ring
      rw [hA, h3]; linarith
    have hB3 : B ≤ 3 := by
      have h3 : sp * (1 - 2 * t) = sp - 2 * (t * sp) := by ring
      rw [hB, h3]; linarith [hF.a2_le]
    have hAB : A ≤ B := by
      rw [hA, hB]
      apply mul_le_mul_of_nonneg_left _ hsp0.le
      linarith [ht.2]
    let f : ℝ → ℝ := fun u => H (sp - sp * t - sp * u) / (u * (1 - t - u))
    have hc : -sp⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hsp0.ne')
    have hsub := intervalIntegral.integral_comp_mul_add (f := f) (a := A) (b := B) hc (1 - t)
    have eA : -sp⁻¹ * A + (1 - t) = 1 / k2 := by rw [hA]; field_simp; ring
    have eB : -sp⁻¹ * B + (1 - t) = t := by rw [hB]; field_simp; ring
    rw [eA, eB, smul_eq_mul, inv_neg, inv_inv] at hsub
    have hsub' : (∫ u in t..(1 / k2), f u) = sp⁻¹ * ∫ v in A..B, f (-sp⁻¹ * v + (1 - t)) := by
      rw [intervalIntegral.integral_symm, hsub, ← mul_assoc,
        show sp⁻¹ * -sp = -1 by field_simp, neg_one_mul]
    have hval : ∀ v, 1 / t * (sp⁻¹ * f (-sp⁻¹ * v + (1 - t))) =
        H v / v * (t * ((1 - v / sp) - t))⁻¹ := by
      intro v
      simp only [f]
      rw [show sp - sp * t - sp * (-sp⁻¹ * v + (1 - t)) = v by field_simp; ring,
        show (-sp⁻¹ * v + (1 - t)) * (1 - t - (-sp⁻¹ * v + (1 - t))) =
          ((1 - v / sp) - t) * v * sp⁻¹ by ring]
      have e : 1 / t * (sp⁻¹ * (H v / (((1 - v / sp) - t) * v * sp⁻¹))) =
          (sp⁻¹ * sp) * (H v / v * (t * ((1 - v / sp) - t))⁻¹) := by
        simp only [div_eq_mul_inv, mul_inv, inv_inv]
        ring
      rw [e, inv_mul_cancel₀ hsp0.ne', one_mul]
    show 1 / t * (∫ u in t..(1 / k2), f u) = _
    rw [hsub', ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    simp only [hval]
    rw [← integral_indicator_Icc (f := fun v => H v / v * (t * ((1 - v / sp) - t))⁻¹)
      (α := 1) (β := 3) hA1 hAB hB3]
    apply intervalIntegral.integral_congr
    intro v hv
    have hmem : v ∈ Icc A B ↔ (t, v) ∈ R := by
      simp only [mem_Icc, R, mem_setOf_eq, hA, hB]
      have hv' : sp * (v / sp) = v := by field_simp
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
    by_cases hm : v ∈ Icc A B
    · rw [indicator_of_mem hm]
      show _ = R.indicator G (t, v)
      rw [indicator_of_mem (hmem.1 hm)]
    · rw [indicator_of_notMem hm]
      show _ = R.indicator G (t, v)
      rw [indicator_of_notMem (fun h' => hm (hmem.2 h'))]
  have hR : MeasurableSet R := by
    apply MeasurableSet.inter
    · exact measurableSet_le (by fun_prop) measurable_fst
    · exact measurableSet_le measurable_fst (by fun_prop)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (1 / sp) (1 / k2))).prod (volume.restrict (Ioc (1 : ℝ) 3))) := by
    have hg2 : Integrable (fun v : ℝ => H v / v) (volume.restrict (Ioc (1 : ℝ) 3)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hKint
    have hbd : Integrable (fun z : ℝ × ℝ => sp ^ 2 * ‖H z.2 / z.2‖)
        ((volume.restrict (Ioc (1 / sp) (1 / k2))).prod (volume.restrict (Ioc (1 : ℝ) 3))) :=
      (integrable_const (sp ^ 2)).mul_prod hg2.norm
    refine hbd.mono' ?_ ?_
    · have hG : AEStronglyMeasurable G
          ((volume.restrict (Ioc (1 / sp) (1 / k2))).prod (volume.restrict (Ioc (1 : ℝ) 3))) :=
        hg2.aestronglyMeasurable.comp_snd.mul
          (Measurable.aestronglyMeasurable
            (f := fun z : ℝ × ℝ => (z.1 * ((1 - z.2 / sp) - z.1))⁻¹) (by fun_prop))
      exact hG.indicator hR
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) ?_
      rintro ⟨t, v⟩ ⟨ht, hv⟩
      simp only [mem_Ioc] at ht hv
      show ‖R.indicator G (t, v)‖ ≤ sp ^ 2 * ‖H v / v‖
      by_cases hm : (t, v) ∈ R
      · rw [indicator_of_mem hm]
        simp only [G, norm_mul, norm_inv]
        have hm2 : t ≤ (1 - v / sp) / 2 := hm.2
        have hq : 1 / sp ^ 2 ≤ t * ((1 - v / sp) - t) := by
          have h1 : 1 / sp ≤ t := ht.1.le
          have h2 : t ≤ (1 - v / sp) - t := by linarith
          calc 1 / sp ^ 2 = 1 / sp * (1 / sp) := by ring
            _ ≤ t * ((1 - v / sp) - t) := mul_le_mul h1 (h1.trans h2) hα0.le (by linarith)
        have hq0 : 0 < t * ((1 - v / sp) - t) := lt_of_lt_of_le (by positivity) hq
        rw [← norm_mul, Real.norm_of_nonneg hq0.le, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [inv_le_comm₀ hq0 (by positivity)]
        simpa [one_div] using hq
      · rw [indicator_of_notMem hm, norm_zero]
        positivity
  rw [intervalIntegral.integral_congr step1, swap13 hαβ hint]
  have hnull : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ ({sp - 2 * sp / k2, sp - sp / k2 - 1,
      sp - 2} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite _).measure_zero _)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hnull] with v hne hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  obtain ⟨n6, n4, n2⟩ := hne
  rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hv
  have hv0 : 0 < v := by linarith [hv.1]
  set q := 1 - v / sp with hq
  have hspq : sp * q = sp - v := by rw [hq]; field_simp
  set T1 := q - 1 / k2 with hT1
  set T2 := q / 2 with hT2
  set w : ℝ → ℝ := fun t => (t * (q - t))⁻¹ with hw
  have hFv : ∀ t, F t v = H v / v * (Icc T1 T2).indicator w t := by
    intro t
    by_cases hm : t ∈ Icc T1 T2
    · rw [indicator_of_mem hm]
      show R.indicator G (t, v) = _
      rw [indicator_of_mem (show (t, v) ∈ R from ⟨by linarith [hm.1], hm.2⟩)]
    · rw [indicator_of_notMem hm, mul_zero]
      show R.indicator G (t, v) = _
      rw [indicator_of_notMem (show (t, v) ∉ R from fun h' => hm ⟨by linarith [h'.1], h'.2⟩)]
  show (∫ t in (1 / sp)..(1 / k2), F t v) = H v * _
  simp only [hFv]
  rw [intervalIntegral.integral_const_mul]
  have hk2' : sp * (1 / k2) = sp / k2 := by ring
  have hsp1 : sp * (1 / sp) = 1 := by field_simp
  -- comparisons, multiplied through by `sp`
  have mul_iff : ∀ a b : ℝ, a ≤ b ↔ sp * a ≤ sp * b := fun a b =>
    ⟨fun h => mul_le_mul_of_nonneg_left h hsp0.le, fun h => le_of_mul_le_mul_left h hsp0⟩
  have eT1 : sp * T1 = sp - v - sp / k2 := by rw [hT1, mul_sub, hspq, hk2']
  have eT2 : sp * T2 = (sp - v) / 2 := by rw [hT2, ← hspq]; ring
  have cT1β : T1 ≤ 1 / k2 ↔ sp - 2 * sp / k2 ≤ v := by
    rw [mul_iff, eT1, hk2', show 2 * sp / k2 = 2 * (sp / k2) by ring]
    constructor <;> intro h <;> linarith
  have cT1α : 1 / sp ≤ T1 ↔ v ≤ sp - sp / k2 - 1 := by
    rw [mul_iff, eT1, hsp1]
    constructor <;> intro h <;> linarith
  have cT2α : 1 / sp ≤ T2 ↔ v ≤ sp - 2 := by
    rw [mul_iff, eT2, hsp1]
    constructor <;> intro h <;> linarith
  have cT2β : T2 ≤ 1 / k2 ↔ sp - 2 * sp / k2 ≤ v := by
    rw [mul_iff, eT2, hk2', show 2 * sp / k2 = 2 * (sp / k2) by ring]
    constructor <;> intro h <;> linarith
  have hq0 : ∀ hv2 : v ≤ sp - 2, 0 < q := fun hv2 => by
    have : 0 < sp * q := by rw [hspq]; linarith
    exact pos_of_mul_pos_right this hsp0.le
  have hlogk2 : log (sp / (k2 * sp - sp - k2 * v)) = -log (k2 * q - 1) := by
    rw [show k2 * q - 1 = (k2 * sp - sp - k2 * v) / sp by rw [hq]; field_simp; ring,
      ← Real.log_inv, inv_div]
  have hlogsp : log (sp - 1 - v) = log (sp * q - 1) := by rw [hspq]; ring_nf
  have hden : ∀ x : ℝ, x / (v * (1 - v / sp)) = x / v / q := by
    intro x; rw [hq, div_div]
  rcases lt_or_gt_of_ne n6 with h6 | h6
  · have hz : (∫ t in (1 / sp)..(1 / k2), (Icc T1 T2).indicator w t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        have hT : ¬ T1 ≤ 1 / k2 := fun h' => by linarith [cT1β.1 h']
        exact indicator_of_notMem (fun hm => hT (hm.1.trans ht.2)) _)]
      simp
    rw [hz]
    have i1 : ¬ (sp - 2 * sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by linarith [h'.1]
    have i2 : ¬ (sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2) := fun h' => by linarith [h'.1]
    simp only [ind, if_neg i1, if_neg i2]
    ring
  rcases lt_or_gt_of_ne n4 with h4 | h4
  · have hqp := hq0 (by linarith)
    have hT1α : 1 / sp ≤ T1 := cT1α.2 h4.le
    have hT2β : T2 ≤ 1 / k2 := cT2β.2 h6.le
    have hT12 : T1 ≤ T2 := by
      have := cT1β.2 h6.le; rw [hT1, hT2] at *; linarith
    have hk2q : 0 < k2 * q - 1 := by
      have : 1 / sp ≤ q - 1 / k2 := hT1α
      have h' : 1 / k2 < q := by linarith [hα0]
      have := mul_lt_mul_of_pos_left h' hk20
      rwa [mul_one_div_cancel hk20.ne'] at this
      |> fun h => by linarith
    have hval : (∫ t in (1 / sp)..(1 / k2), (Icc T1 T2).indicator w t) =
        ((log T2 - log (q - T2)) - (log T1 - log (q - T1))) / q := by
      rw [integral_indicator_Icc hT1α hT12 hT2β,
        wq_integral (hα0.trans_le hT1α) hT12 (by rw [hT2]; linarith)]
    rw [hval, hT2, hT1, Fq_half, Fq_sub hk20 hk2q]
    have i1 : sp - 2 * sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1 := ⟨h6.le, h4.le⟩
    have i2 : ¬ (sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2) := fun h' => by linarith [h'.1]
    simp only [ind, if_pos i1, if_neg i2, hlogk2, hden]
    ring
  rcases lt_or_gt_of_ne n2 with h2 | h2
  · have hqp := hq0 h2.le
    have hT2α : 1 / sp ≤ T2 := cT2α.2 h2.le
    have hT2β : T2 ≤ 1 / k2 := cT2β.2 (by linarith)
    have hT1α : T1 < 1 / sp := by
      by_contra hc; exact absurd (cT1α.1 (not_lt.1 hc)) (by linarith)
    have hspq1 : 0 < sp * q - 1 := by rw [hspq]; linarith
    have hval : (∫ t in (1 / sp)..(1 / k2), (Icc T1 T2).indicator w t) =
        ((log T2 - log (q - T2)) - (log (1 / sp) - log (q - 1 / sp))) / q := by
      rw [intervalIntegral.integral_congr (g := (Icc (1 / sp) T2).indicator w) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        by_cases hm : t ∈ Icc (1 / sp) T2
        · rw [indicator_of_mem hm,
            indicator_of_mem (show t ∈ Icc T1 T2 from ⟨hT1α.le.trans hm.1, hm.2⟩)]
        · rw [indicator_of_notMem hm, indicator_of_notMem
            (fun (h' : t ∈ Icc T1 T2) => hm ⟨ht.1, h'.2⟩)]),
        integral_indicator_Icc le_rfl hT2α hT2β,
        wq_integral hα0 hT2α (by rw [hT2]; linarith)]
    rw [hval, hT2, Fq_half, Fq_one_div hsp0 hspq1]
    have i1 : ¬ (sp - 2 * sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by linarith [h'.2]
    have i2 : sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2 := ⟨h4.le, h2.le⟩
    simp only [ind, if_neg i1, if_pos i2, hlogsp, hden]
    ring
  · have hz : (∫ t in (1 / sp)..(1 / k2), (Icc T1 T2).indicator w t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        have hT : ¬ 1 / sp ≤ T2 := fun h' => by linarith [cT2α.1 h']
        exact indicator_of_notMem (fun hm => hT (ht.1.trans hm.2)) _)]
      simp
    rw [hz]
    have i1 : ¬ (sp - 2 * sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by linarith [h'.2]
    have i2 : ¬ (sp - sp / k2 - 1 ≤ v ∧ v ≤ sp - 2) := fun h' => by linarith [h'.2]
    simp only [ind, if_neg i1, if_neg i2]
    ring

/-- **Display 6.7 PROVED**, formerly a sub-leaf of `proposition4`. Wu 2004 page 29, "similarly":
the change of variable `v = s'(1 − t − u)` and an interchange of the order of integration give
`D₂ = ∫₁³ H(t) L₁(t) dt`. -/
theorem eq67 {H : ℝ → ℝ} (hH : AntitoneOn H (Icc (1 : ℝ) 3)) {p : Params}
    (hp : Admissible4 p) : D2 H p = ∫ t in (1 : ℝ)..3, H t * L1 p t := by
  obtain ⟨s, sp, k1, k2, k3⟩ := p
  have hF := adm4_facts hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := alpha_vals s sp k1 k2 k3
  have a6 : 1 ≤ sp - sp / k1 - sp / k3 := by
    have := (hp.2.2.2.2.2.1 6).1; rwa [e6] at this
  have h58 : sp - sp / k3 - 1 < sp - sp / k1 - sp / k2 := by
    have := hp.2.2.2.2.2.2.2; rwa [e4, e7] at this
  have hk3 : 2 ≤ k3 := by linarith [hF.s2, hF.sk3]
  have hk30 : 0 < k3 := by linarith
  have hk20 : 0 < k2 := by linarith [hF.k32]
  have hk10 : 0 < k1 := by linarith [hF.k32, hF.k21]
  have hsp0 : 0 < sp := by linarith [hF.sp3]
  have hαβ : 1 / sp ≤ 1 / k1 := one_div_le_one_div_of_le hk10 hF.k1sp
  have hα0 : 0 < 1 / sp := by positivity
  have hKint := H_div_integrable hH
  have o42 := hF.a4_le_a2
  have o84 := hF.a8_le_a4
  have o75 : sp - sp / k1 - sp / k3 ≤ sp - sp / k3 - 1 := by
    have : 1 ≤ sp / k1 := (one_le_div hk10).2 hF.k1sp
    linarith
  have h1k2 : 1 / k2 ≤ 1 / k3 := one_div_le_one_div_of_le hk30 hF.k32.le
  unfold D2 L1
  simp only [e3, e4, e6, e7]
  let R : Set (ℝ × ℝ) := {z | 1 - z.2 / sp - 1 / k3 ≤ z.1 ∧ z.1 ≤ 1 - z.2 / sp - 1 / k2}
  let G : ℝ × ℝ → ℝ := fun z => H z.2 / z.2 * (z.1 * ((1 - z.2 / sp) - z.1))⁻¹
  let F : ℝ → ℝ → ℝ := fun t v => R.indicator G (t, v)
  have step1 : ∀ t ∈ uIcc (1 / sp) (1 / k1),
      1 / t * (∫ u in (1 / k2)..(1 / k3), H (sp - sp * t - sp * u) / (u * (1 - t - u))) =
        ∫ v in (1 : ℝ)..3, F t v := by
    intro t ht
    rw [uIcc_of_le hαβ] at ht
    have ht0 : 0 < t := hα0.trans_le ht.1
    have htsp : 1 ≤ t * sp := by
      have := mul_le_mul_of_nonneg_right ht.1 hsp0.le
      rwa [one_div_mul_cancel hsp0.ne'] at this
    set A := sp * (1 - t - 1 / k3) with hA
    set B := sp * (1 - t - 1 / k2) with hB
    have hA1 : 1 ≤ A := by
      have h1 : sp * t ≤ sp * (1 / k1) := mul_le_mul_of_nonneg_left ht.2 hsp0.le
      have h3 : sp * (1 - t - 1 / k3) = sp - sp * t - sp * (1 / k3) := by ring
      have h4 : sp * (1 / k1) = sp / k1 := by ring
      have h5 : sp * (1 / k3) = sp / k3 := by ring
      rw [hA, h3]; linarith
    have hB3 : B ≤ 3 := by
      have h3 : sp * (1 - t - 1 / k2) = sp - t * sp - sp / k2 := by ring
      rw [hB, h3]; linarith [hF.a2_le]
    have hAB : A ≤ B := by
      rw [hA, hB]
      apply mul_le_mul_of_nonneg_left _ hsp0.le
      linarith
    let f : ℝ → ℝ := fun u => H (sp - sp * t - sp * u) / (u * (1 - t - u))
    have hc : -sp⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hsp0.ne')
    have hsub := intervalIntegral.integral_comp_mul_add (f := f) (a := A) (b := B) hc (1 - t)
    have eA : -sp⁻¹ * A + (1 - t) = 1 / k3 := by rw [hA]; field_simp; ring
    have eB : -sp⁻¹ * B + (1 - t) = 1 / k2 := by rw [hB]; field_simp; ring
    rw [eA, eB, smul_eq_mul, inv_neg, inv_inv] at hsub
    have hsub' : (∫ u in (1 / k2)..(1 / k3), f u) =
        sp⁻¹ * ∫ v in A..B, f (-sp⁻¹ * v + (1 - t)) := by
      rw [intervalIntegral.integral_symm, hsub, ← mul_assoc,
        show sp⁻¹ * -sp = -1 by field_simp, neg_one_mul]
    have hval : ∀ v, 1 / t * (sp⁻¹ * f (-sp⁻¹ * v + (1 - t))) =
        H v / v * (t * ((1 - v / sp) - t))⁻¹ := by
      intro v
      simp only [f]
      rw [show sp - sp * t - sp * (-sp⁻¹ * v + (1 - t)) = v by field_simp; ring,
        show (-sp⁻¹ * v + (1 - t)) * (1 - t - (-sp⁻¹ * v + (1 - t))) =
          ((1 - v / sp) - t) * v * sp⁻¹ by ring]
      have e : 1 / t * (sp⁻¹ * (H v / (((1 - v / sp) - t) * v * sp⁻¹))) =
          (sp⁻¹ * sp) * (H v / v * (t * ((1 - v / sp) - t))⁻¹) := by
        simp only [div_eq_mul_inv, mul_inv, inv_inv]
        ring
      rw [e, inv_mul_cancel₀ hsp0.ne', one_mul]
    show 1 / t * (∫ u in (1 / k2)..(1 / k3), f u) = _
    rw [hsub', ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    simp only [hval]
    rw [← integral_indicator_Icc (f := fun v => H v / v * (t * ((1 - v / sp) - t))⁻¹)
      (α := 1) (β := 3) hA1 hAB hB3]
    apply intervalIntegral.integral_congr
    intro v hv
    have hmem : v ∈ Icc A B ↔ (t, v) ∈ R := by
      simp only [mem_Icc, R, mem_setOf_eq, hA, hB]
      have hv' : sp * (v / sp) = v := by field_simp
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
    by_cases hm : v ∈ Icc A B
    · rw [indicator_of_mem hm]
      show _ = R.indicator G (t, v)
      rw [indicator_of_mem (hmem.1 hm)]
    · rw [indicator_of_notMem hm]
      show _ = R.indicator G (t, v)
      rw [indicator_of_notMem (fun h' => hm (hmem.2 h'))]
  have hR : MeasurableSet R := by
    apply MeasurableSet.inter
    · exact measurableSet_le (by fun_prop) measurable_fst
    · exact measurableSet_le measurable_fst (by fun_prop)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (1 / sp) (1 / k1))).prod (volume.restrict (Ioc (1 : ℝ) 3))) := by
    have hg2 : Integrable (fun v : ℝ => H v / v) (volume.restrict (Ioc (1 : ℝ) 3)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hKint
    have hbd : Integrable (fun z : ℝ × ℝ => sp ^ 2 * ‖H z.2 / z.2‖)
        ((volume.restrict (Ioc (1 / sp) (1 / k1))).prod (volume.restrict (Ioc (1 : ℝ) 3))) :=
      (integrable_const (sp ^ 2)).mul_prod hg2.norm
    refine hbd.mono' ?_ ?_
    · have hG : AEStronglyMeasurable G
          ((volume.restrict (Ioc (1 / sp) (1 / k1))).prod (volume.restrict (Ioc (1 : ℝ) 3))) :=
        hg2.aestronglyMeasurable.comp_snd.mul
          (Measurable.aestronglyMeasurable
            (f := fun z : ℝ × ℝ => (z.1 * ((1 - z.2 / sp) - z.1))⁻¹) (by fun_prop))
      exact hG.indicator hR
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) ?_
      rintro ⟨t, v⟩ ⟨ht, hv⟩
      simp only [mem_Ioc] at ht hv
      show ‖R.indicator G (t, v)‖ ≤ sp ^ 2 * ‖H v / v‖
      by_cases hm : (t, v) ∈ R
      · rw [indicator_of_mem hm]
        simp only [G, norm_mul, norm_inv]
        have hm2 : t ≤ 1 - v / sp - 1 / k2 := hm.2
        have hk2sp : 1 / sp ≤ 1 / k2 :=
          one_div_le_one_div_of_le hk20 (by linarith [hF.k21, hF.k1sp])
        have hq : 1 / sp ^ 2 ≤ t * ((1 - v / sp) - t) := by
          have h1 : 1 / sp ≤ t := ht.1.le
          have h2 : 1 / sp ≤ (1 - v / sp) - t := by linarith
          calc 1 / sp ^ 2 = 1 / sp * (1 / sp) := by ring
            _ ≤ t * ((1 - v / sp) - t) := mul_le_mul h1 h2 hα0.le (by linarith)
        have hq0 : 0 < t * ((1 - v / sp) - t) := lt_of_lt_of_le (by positivity) hq
        rw [← norm_mul, Real.norm_of_nonneg hq0.le, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [inv_le_comm₀ hq0 (by positivity)]
        simpa [one_div] using hq
      · rw [indicator_of_notMem hm, norm_zero]
        positivity
  rw [intervalIntegral.integral_congr step1, swap13 hαβ hint]
  have hnull : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ ({sp - sp / k1 - sp / k3, sp - sp / k3 - 1,
      sp - sp / k1 - sp / k2, sp - sp / k2 - 1} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite _).measure_zero _)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hnull] with v hne hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  obtain ⟨n7, n5, n8, n4⟩ := hne
  rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hv
  have hv0 : 0 < v := by linarith [hv.1]
  set q := 1 - v / sp with hq
  have hspq : sp * q = sp - v := by rw [hq]; field_simp
  set T1 := q - 1 / k3 with hT1
  set T2 := q - 1 / k2 with hT2
  set w : ℝ → ℝ := fun t => (t * (q - t))⁻¹ with hw
  have hFv : ∀ t, F t v = H v / v * (Icc T1 T2).indicator w t := by
    intro t
    by_cases hm : t ∈ Icc T1 T2
    · rw [indicator_of_mem hm]
      show R.indicator G (t, v) = _
      rw [indicator_of_mem (show (t, v) ∈ R from ⟨by linarith [hm.1], by linarith [hm.2]⟩)]
    · rw [indicator_of_notMem hm, mul_zero]
      show R.indicator G (t, v) = _
      rw [indicator_of_notMem (show (t, v) ∉ R from
        fun h' => hm ⟨by linarith [h'.1], by linarith [h'.2]⟩)]
  show (∫ t in (1 / sp)..(1 / k1), F t v) = H v * _
  simp only [hFv]
  rw [intervalIntegral.integral_const_mul]
  have hsp1 : sp * (1 / sp) = 1 := by field_simp
  have mul_iff : ∀ a b : ℝ, a ≤ b ↔ sp * a ≤ sp * b := fun a b =>
    ⟨fun h => mul_le_mul_of_nonneg_left h hsp0.le, fun h => le_of_mul_le_mul_left h hsp0⟩
  have eT1 : sp * T1 = sp - v - sp / k3 := by
    rw [hT1, mul_sub, hspq, show sp * (1 / k3) = sp / k3 by ring]
  have eT2 : sp * T2 = sp - v - sp / k2 := by
    rw [hT2, mul_sub, hspq, show sp * (1 / k2) = sp / k2 by ring]
  have ek1 : sp * (1 / k1) = sp / k1 := by ring
  have cT1β : T1 ≤ 1 / k1 ↔ sp - sp / k1 - sp / k3 ≤ v := by
    rw [mul_iff, eT1, ek1]; constructor <;> intro h <;> linarith
  have cT1α : 1 / sp ≤ T1 ↔ v ≤ sp - sp / k3 - 1 := by
    rw [mul_iff, eT1, hsp1]; constructor <;> intro h <;> linarith
  have cT2β : T2 ≤ 1 / k1 ↔ sp - sp / k1 - sp / k2 ≤ v := by
    rw [mul_iff, eT2, ek1]; constructor <;> intro h <;> linarith
  have cT2α : 1 / sp ≤ T2 ↔ v ≤ sp - sp / k2 - 1 := by
    rw [mul_iff, eT2, hsp1]; constructor <;> intro h <;> linarith
  have hX : ∀ k : ℝ, k * sp - sp - k * v = sp * (k * q - 1) := fun k => by
    rw [hq]; field_simp; ring
  have hs1 : sp - 1 - v = sp * q - 1 := by rw [hspq]; ring
  have hden : ∀ x : ℝ, x / (v * (1 - v / sp)) = x / v / q := by
    intro x; rw [hq, div_div]
  have hk1q : ∀ (hT2β : 1 / k1 < T2 ∨ 1 / sp ≤ T1), 0 < k1 * q - 1 := by
    intro h
    have h' : 1 / k1 < q := by
      rcases h with h | h
      · have : 0 < 1 / k2 := by positivity
        linarith
      · have : 1 / k1 ≤ 1 / k3 := one_div_le_one_div_of_le hk30 (hF.k32.trans hF.k21).le
        linarith
    have := mul_lt_mul_of_pos_left h' hk10
    rw [mul_one_div_cancel hk10.ne'] at this
    linarith
  rcases lt_or_gt_of_ne n7 with h7 | h7
  · have hz : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        have hT : ¬ T1 ≤ 1 / k1 := fun h' => by linarith [cT1β.1 h']
        exact indicator_of_notMem (fun hm => hT (hm.1.trans ht.2)) _)]
      simp
    rw [hz]
    have i1 : ¬ (sp - sp / k1 - sp / k3 ≤ v ∧ v ≤ sp - sp / k3 - 1) := fun h' => by linarith [h'.1]
    have i2 : ¬ (sp - sp / k3 - 1 ≤ v ∧ v ≤ sp - sp / k1 - sp / k2) := fun h' => by
      linarith [h'.1]
    have i3 : ¬ (sp - sp / k1 - sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by
      linarith [h'.1]
    simp only [ind, if_neg i1, if_neg i2, if_neg i3]
    ring
  rcases lt_or_gt_of_ne n5 with h5 | h5
  · have hT1α : 1 / sp ≤ T1 := cT1α.2 h5.le
    have hT1β : T1 ≤ 1 / k1 := cT1β.2 h7.le
    have hT2β : 1 / k1 < T2 := by
      by_contra hc; exact absurd (cT2β.1 (not_lt.1 hc)) (by linarith)
    have hk3q : 0 < k3 * q - 1 := by
      have h' : 1 / k3 < q := by rw [hT1] at hT1α; linarith
      have := mul_lt_mul_of_pos_left h' hk30
      rw [mul_one_div_cancel hk30.ne'] at this
      linarith
    have hk1q' := hk1q (Or.inl hT2β)
    have hval : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) =
        ((log (1 / k1) - log (q - 1 / k1)) - (log T1 - log (q - T1))) / q := by
      rw [intervalIntegral.integral_congr (g := (Icc T1 (1 / k1)).indicator w) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        by_cases hm : t ∈ Icc T1 (1 / k1)
        · rw [indicator_of_mem hm,
            indicator_of_mem (show t ∈ Icc T1 T2 from ⟨hm.1, hm.2.trans hT2β.le⟩)]
        · rw [indicator_of_notMem hm, indicator_of_notMem
            (fun (h' : t ∈ Icc T1 T2) => hm ⟨h'.1, ht.2⟩)]),
        integral_indicator_Icc hT1α hT1β le_rfl,
        wq_integral (hα0.trans_le hT1α) hT1β (by
          have : 0 < 1 / k2 := by positivity
          rw [hT2] at hT2β; linarith)]
    rw [hval, hT1, Fq_sub hk30 hk3q, Fq_one_div hk10 hk1q']
    have i1 : sp - sp / k1 - sp / k3 ≤ v ∧ v ≤ sp - sp / k3 - 1 := ⟨h7.le, h5.le⟩
    have i2 : ¬ (sp - sp / k3 - 1 ≤ v ∧ v ≤ sp - sp / k1 - sp / k2) := fun h' => by
      linarith [h'.1]
    have i3 : ¬ (sp - sp / k1 - sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by
      linarith [h'.1]
    simp only [ind, if_pos i1, if_neg i2, if_neg i3, hden, hX]
    rw [show sp ^ 2 / (sp * (k1 * q - 1) * (sp * (k3 * q - 1))) =
      ((k1 * q - 1) * (k3 * q - 1))⁻¹ by field_simp, Real.log_inv,
      log_mul hk1q'.ne' hk3q.ne']
    ring
  rcases lt_or_gt_of_ne n8 with h8 | h8
  · have hT1α : T1 < 1 / sp := by
      by_contra hc; exact absurd (cT1α.1 (not_lt.1 hc)) (by linarith)
    have hT2β : 1 / k1 < T2 := by
      by_contra hc; exact absurd (cT2β.1 (not_lt.1 hc)) (by linarith)
    have hk1q' := hk1q (Or.inl hT2β)
    have hspq1 : 0 < sp * q - 1 := by rw [hspq]; linarith
    have hval : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) =
        ((log (1 / k1) - log (q - 1 / k1)) - (log (1 / sp) - log (q - 1 / sp))) / q := by
      rw [intervalIntegral.integral_congr (g := (Icc (1 / sp) (1 / k1)).indicator w)
        (fun t ht => by
          rw [uIcc_of_le hαβ] at ht
          rw [indicator_of_mem ht,
            indicator_of_mem (show t ∈ Icc T1 T2 from ⟨hT1α.le.trans ht.1, ht.2.trans hT2β.le⟩)]),
        integral_indicator_Icc le_rfl hαβ le_rfl,
        wq_integral hα0 hαβ (by
          have : 0 < 1 / k2 := by positivity
          rw [hT2] at hT2β; linarith)]
    rw [hval, Fq_one_div hk10 hk1q', Fq_one_div hsp0 hspq1]
    have i1 : ¬ (sp - sp / k1 - sp / k3 ≤ v ∧ v ≤ sp - sp / k3 - 1) := fun h' => by
      linarith [h'.2]
    have i2 : sp - sp / k3 - 1 ≤ v ∧ v ≤ sp - sp / k1 - sp / k2 := ⟨h5.le, h8.le⟩
    have i3 : ¬ (sp - sp / k1 - sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by
      linarith [h'.1]
    simp only [ind, if_neg i1, if_pos i2, if_neg i3, hden, hX, hs1]
    rw [show sp * (sp * q - 1) / (sp * (k1 * q - 1)) = (sp * q - 1) / (k1 * q - 1) by
      field_simp, log_div hspq1.ne' hk1q'.ne']
    ring
  rcases lt_or_gt_of_ne n4 with h4 | h4
  · have hT1α : T1 < 1 / sp := by
      by_contra hc; exact absurd (cT1α.1 (not_lt.1 hc)) (by linarith)
    have hT2α : 1 / sp ≤ T2 := cT2α.2 h4.le
    have hT2β : T2 ≤ 1 / k1 := cT2β.2 h8.le
    have hspq1 : 0 < sp * q - 1 := by rw [hspq]; linarith
    have hk2q : 0 < k2 * q - 1 := by
      have h' : 1 / k2 < q := by rw [hT2] at hT2α; linarith
      have := mul_lt_mul_of_pos_left h' hk20
      rw [mul_one_div_cancel hk20.ne'] at this
      linarith
    have hval : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) =
        ((log T2 - log (q - T2)) - (log (1 / sp) - log (q - 1 / sp))) / q := by
      rw [intervalIntegral.integral_congr (g := (Icc (1 / sp) T2).indicator w) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        by_cases hm : t ∈ Icc (1 / sp) T2
        · rw [indicator_of_mem hm,
            indicator_of_mem (show t ∈ Icc T1 T2 from ⟨hT1α.le.trans hm.1, hm.2⟩)]
        · rw [indicator_of_notMem hm, indicator_of_notMem
            (fun (h' : t ∈ Icc T1 T2) => hm ⟨ht.1, h'.2⟩)]),
        integral_indicator_Icc le_rfl hT2α hT2β,
        wq_integral hα0 hT2α (by
          have : 0 < 1 / k2 := by positivity
          rw [hT2]; linarith)]
    rw [hval, hT2, Fq_sub hk20 hk2q, Fq_one_div hsp0 hspq1]
    have i1 : ¬ (sp - sp / k1 - sp / k3 ≤ v ∧ v ≤ sp - sp / k3 - 1) := fun h' => by
      linarith [h'.2]
    have i2 : ¬ (sp - sp / k3 - 1 ≤ v ∧ v ≤ sp - sp / k1 - sp / k2) := fun h' => by
      linarith [h'.2]
    have i3 : sp - sp / k1 - sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1 := ⟨h8.le, h4.le⟩
    simp only [ind, if_neg i1, if_neg i2, if_pos i3, hden, hX, hs1]
    rw [show (sp * q - 1) * (sp * (k2 * q - 1)) / sp = (sp * q - 1) * (k2 * q - 1) by
      field_simp, log_mul hspq1.ne' hk2q.ne']
    ring
  · have hz : (∫ t in (1 / sp)..(1 / k1), (Icc T1 T2).indicator w t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
        rw [uIcc_of_le hαβ] at ht
        have hT : ¬ 1 / sp ≤ T2 := fun h' => by linarith [cT2α.1 h']
        exact indicator_of_notMem (fun hm => hT (ht.1.trans hm.2)) _)]
      simp
    rw [hz]
    have i1 : ¬ (sp - sp / k1 - sp / k3 ≤ v ∧ v ≤ sp - sp / k3 - 1) := fun h' => by
      linarith [h'.2]
    have i2 : ¬ (sp - sp / k3 - 1 ≤ v ∧ v ≤ sp - sp / k1 - sp / k2) := fun h' => by
      linarith [h'.2]
    have i3 : ¬ (sp - sp / k1 - sp / k2 ≤ v ∧ v ≤ sp - sp / k2 - 1) := fun h' => by
      linarith [h'.2]
    simp only [ind, if_neg i1, if_neg i2, if_neg i3]
    ring

/-- The "simple calculation" of page 30 behind Proposition 4, pointwise off three points:
`Ξ₂(t; s) = (1/5) (4 K₂(s') + K₂(κ₁) + Σ_{x ∈ {s, κ₂, κ₃}} (log((s'−1)/(x−1)) K₃ₐ + K₃ᵦ(x))
  + L66 + L₁ + L₂)`, where `K₂` is the kernel of 6.2, `K₃ₐ`, `K₃ᵦ` those of 6.3 at
`a = 1 − 1/x`, `b = 1 − 1/s'`, `c = s'`, and `L66`, `L₁`, `L₂` those of 6.6 to 6.8. The
first two lines of this sum make up display 6.5. -/
theorem Xi2_split {s sp k1 k2 k3 : ℝ} (hp : Admissible4 ⟨s, sp, k1, k2, k3⟩) {t : ℝ}
    (ht1 : 1 ≤ t) (hne2 : t ≠ sp - 2) (hne4 : t ≠ sp - sp / k2 - 1)
    (hne8 : t ≠ sp - sp / k1 - sp / k2) :
    Xi2 ⟨s, sp, k1, k2, k3⟩ t = 1 / 5 * (4 * kernel62 sp t + kernel62 k1 t +
      log ((sp - 1) / (s - 1)) * kernel63a sp t + kernel63b s sp t +
      log ((sp - 1) / (k2 - 1)) * kernel63a sp t + kernel63b k2 sp t +
      log ((sp - 1) / (k3 - 1)) * kernel63a sp t + kernel63b k3 sp t +
      L66 ⟨s, sp, k1, k2, k3⟩ t + L1 ⟨s, sp, k1, k2, k3⟩ t + L2 ⟨s, sp, k1, k2, k3⟩ t) := by
  have hF := adm4_facts hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := alpha_vals s sp k1 k2 k3
  simp only [Xi2, kernel62, kernel63a, kernel63b, L66, L1, L2, e0, e1, e2, e3, e4, e5, e6, e7, e8]
  have hs1 : s - 1 ≠ 0 := by linarith [hF.s2]
  have hsp1 : sp - 1 ≠ 0 := by linarith [hF.sp3]
  have hk11 : k1 - 1 ≠ 0 := by linarith [hF.k1_3]
  have hk21 : k2 - 1 ≠ 0 := by linarith [hF.s2, hF.sk3, hF.k32]
  have hk31 : k3 - 1 ≠ 0 := by linarith [hF.s2, hF.sk3]
  have hsp0 : sp ≠ 0 := by linarith [hF.sp3]
  have ht0 : t + 1 ≠ 0 := by linarith
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  -- unconditional logarithms
  have u1 : log (1024 / ((s - 1) * (sp - 1) * (k1 - 1) * (k2 - 1) * (k3 - 1))) =
      10 * log 2 - (log (s - 1) + log (sp - 1) + log (k1 - 1) + log (k2 - 1) + log (k3 - 1)) := by
    rw [log_div (by norm_num) (by simp [*]), log_mul (by simp [*]) hk31, log_mul (by simp [*]) hk21,
      log_mul (by simp [*]) hk11, log_mul hs1 hsp1, show (1024 : ℝ) = 2 ^ 10 by norm_num, log_pow]
    push_cast; ring
  have u2 : log ((t + 1) ^ 5 / ((s - 1) * (sp - 1) * (k1 - 1) * (k2 - 1) * (k3 - 1))) =
      5 * log (t + 1) -
        (log (s - 1) + log (sp - 1) + log (k1 - 1) + log (k2 - 1) + log (k3 - 1)) := by
    rw [log_div (by simp [*]) (by simp [*]), log_mul (by simp [*]) hk31, log_mul (by simp [*]) hk21,
      log_mul (by simp [*]) hk11, log_mul hs1 hsp1, log_pow]
    push_cast; ring
  have u3 : log ((t + 1) ^ 2 / ((k1 - 1) * (k2 - 1))) =
      2 * log (t + 1) - (log (k1 - 1) + log (k2 - 1)) := by
    rw [log_div (by simp [*]) (by simp [*]), log_mul hk11 hk21, log_pow]; push_cast; ring
  have u4 (x : ℝ) (hx : x - 1 ≠ 0) : log (4 / (x - 1)) = 2 * log 2 - log (x - 1) := by
    rw [log_div (by norm_num) hx, show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring
  have u5 (x : ℝ) (hx : x - 1 ≠ 0) : log ((t + 1) / (x - 1)) = log (t + 1) - log (x - 1) :=
    log_div ht0 hx
  have u6 (x : ℝ) (hx : x - 1 ≠ 0) : log ((sp - 1) / (x - 1)) = log (sp - 1) - log (x - 1) :=
    log_div hsp1 hx
  -- logarithms that split on their supports
  have c1 := ind_mul_eq_all (a := k1 - k1 / k2 - 1) (b := k1 - 2) (t := t)
    (u := log ((t + 1) / ((k2 - 1) * (k1 - 1 - t))))
    (v := log (t + 1) - log (k2 - 1) - log (k1 - 1 - t)) (fun _ hb => by
      rw [log_div ht0 (mul_ne_zero hk21 (by linarith)), log_mul hk21 (by linarith)]; ring)
  have csp (x : ℝ) (hx : x - 1 ≠ 0) (a : ℝ) := ind_mul_eq_all (a := a) (b := sp - 2) (t := t)
    (u := log ((t + 1) / ((x - 1) * (sp - 1 - t))))
    (v := log (t + 1) - log (x - 1) - log (sp - 1 - t)) (fun _ hb => by
      rw [log_div ht0 (mul_ne_zero hx (by linarith)), log_mul hx (by linarith)]; ring)
  have c6 := ind_mul_eq_all (a := sp - sp / k1 - sp / k3) (b := sp - sp / k3 - 1) (t := t)
    (u := log (sp ^ 2 / ((k1 * sp - sp - k1 * t) * (k3 * sp - sp - k3 * t))))
    (v := 2 * log sp - log (k1 * sp - sp - k1 * t) - log (k3 * sp - sp - k3 * t))
    (fun _ hb => by
      have := hF.X1_of_a5 t hb
      have := hF.X3_of_a5 t hb
      rw [log_div (pow_ne_zero 2 hsp0) (by positivity), log_mul (by positivity) (by positivity),
        log_pow]; push_cast; ring)
  have c7 := ind_mul_eq_all (a := sp - sp / k3 - 1) (b := sp - sp / k1 - sp / k2) (t := t)
    (u := log (sp * (sp - 1 - t) / (k1 * sp - sp - k1 * t)))
    (v := log sp + log (sp - 1 - t) - log (k1 * sp - sp - k1 * t))
    (fun _ hb => by
      have := hF.X1_of_a8 t hb
      have : sp - 1 - t ≠ 0 := by linarith [hF.a8_le_a4, hF.a4_le_a2]
      rw [log_div (mul_ne_zero hsp0 this) (by positivity), log_mul hsp0 this])
  have c8 := ind_mul_eq_all (a := sp - 2 * sp / k2) (b := sp - sp / k1 - sp / k2) (t := t)
    (u := log (sp / (k2 * sp - sp - k2 * t))) (v := log sp - log (k2 * sp - sp - k2 * t))
    (fun _ hb => by
      have := hF.X2_of_a4 t (hb.trans hF.a8_le_a4)
      rw [log_div hsp0 (by positivity)])
  have c9 := ind_mul_eq_all (a := sp - 2 * sp / k2) (b := sp - sp / k2 - 1) (t := t)
    (u := log (sp / (k2 * sp - sp - k2 * t))) (v := log sp - log (k2 * sp - sp - k2 * t))
    (fun _ hb => by
      have := hF.X2_of_a4 t hb
      rw [log_div hsp0 (by positivity)])
  have c10 := ind_mul_eq_all (a := sp - sp / k1 - sp / k2) (b := sp - sp / k2 - 1) (t := t)
    (u := log ((sp - 1 - t) * (k2 * sp - sp - k2 * t) / sp))
    (v := log (sp - 1 - t) + log (k2 * sp - sp - k2 * t) - log sp)
    (fun _ hb => by
      have := hF.X2_of_a4 t hb
      have : sp - 1 - t ≠ 0 := by linarith [hF.a4_le_a2]
      rw [log_div (mul_ne_zero this (by positivity)) hsp0, log_mul this (by positivity)])
  simp only [u1, u2, u3, u4 sp hsp1, u4 k1 hk11, u5 sp hsp1, u5 k1 hk11, u5 k2 hk21,
    u6 s hs1, u6 k2 hk21, u6 k3 hk31, c1, csp s hs1, csp k2 hk21, csp k3 hk31, c6, c7, c8, c9, c10]
  -- split the support intervals
  rw [ind_split (a := k1 - 2) (m := sp - 2) (b := 3) (by linarith [hF.k1sp]) hF.a2_le hne2,
    ind_split (a := k1 - 2) (m := sp - sp / k2 - 1) (b := sp - 2) hF.a1_lt_a4.le hF.a4_le_a2 hne4,
    ind_split (a := sp - 2 * sp / k2) (m := sp - sp / k1 - sp / k2) (b := sp - sp / k2 - 1)
      hF.a6_le_a8 hF.a8_le_a4 hne8,
    ind_split (a := sp - sp / k1 - sp / k2) (m := sp - sp / k2 - 1) (b := sp - 2)
      hF.a8_le_a4 hF.a4_le_a2 hne4]
  rw [show 5 * t * (1 - t / sp) = 5 * (t * (1 - t / sp)) by ring]
  generalize t * (1 - t / sp) = q
  ring

/-! #### Integrability of the kernels of displays 6.6 to 6.8 -/

theorem q_ne {sp t : ℝ} (ht1 : 1 ≤ t) (ht : t ≤ sp - 2) : t * (1 - t / sp) ≠ 0 := by
  have hsp : 0 < sp := by linarith
  have : t / sp < 1 := (div_lt_one hsp).2 (by linarith)
  exact (mul_pos (by linarith) (by linarith)).ne'

theorem L66_integrable {s sp k1 k2 k3 : ℝ} (hp : Admissible4 ⟨s, sp, k1, k2, k3⟩) :
    IntervalIntegrable (L66 ⟨s, sp, k1, k2, k3⟩) volume 1 3 := by
  have hF := adm4_facts hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := alpha_vals s sp k1 k2 k3
  unfold L66
  simp only [e1, e3, e5]
  refine IntervalIntegrable.add ?_ ?_
  · apply ind_log_integrable (by fun_prop)
      (fun t ht => q_ne ht.2.1 (ht.1.2.trans hF.a4_le_a2))
    · exact ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun t ht => (hF.X2_of_a4 t ht.1.2).ne')
    · intro t ht
      exact (div_pos (by linarith [hF.sp3]) (hF.X2_of_a4 t ht.1.2)).ne'
  · apply ind_log_integrable (by fun_prop) (fun t ht => q_ne ht.2.1 ht.1.2) (by fun_prop)
    intro t ht
    exact (show (0 : ℝ) < sp - 1 - t by linarith [ht.1.2]).ne'

theorem L1_integrable {s sp k1 k2 k3 : ℝ} (hp : Admissible4 ⟨s, sp, k1, k2, k3⟩) :
    IntervalIntegrable (L1 ⟨s, sp, k1, k2, k3⟩) volume 1 3 := by
  have hF := adm4_facts hp
  have h5 : sp - sp / k3 - 1 ≤ sp - 2 := by
    have hk3p : 0 < k3 := by linarith [hF.s2, hF.sk3]
    have : 1 ≤ sp / k3 := (one_le_div hk3p).2 (by linarith [hF.k32, hF.k21, hF.k1sp])
    linarith
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := alpha_vals s sp k1 k2 k3
  unfold L1
  simp only [e3, e4, e6, e7]
  refine IntervalIntegrable.add (IntervalIntegrable.add ?_ ?_) ?_
  · apply ind_log_integrable (by fun_prop)
      (fun t ht => q_ne ht.2.1 (ht.1.2.trans h5))
    · exact ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun t ht => (mul_pos (hF.X1_of_a5 t ht.1.2) (hF.X3_of_a5 t ht.1.2)).ne')
    · intro t ht
      exact (div_pos (by nlinarith [hF.sp3])
        (mul_pos (hF.X1_of_a5 t ht.1.2) (hF.X3_of_a5 t ht.1.2))).ne'
  · apply ind_log_integrable (by fun_prop)
      (fun t ht => q_ne ht.2.1 (ht.1.2.trans (hF.a8_le_a4.trans hF.a4_le_a2)))
    · exact ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun t ht => (hF.X1_of_a8 t ht.1.2).ne')
    · intro t ht
      have : 0 < sp - 1 - t := by linarith [ht.1.2, hF.a8_le_a4, hF.a4_le_a2]
      exact (div_pos (mul_pos (by linarith [hF.sp3]) this) (hF.X1_of_a8 t ht.1.2)).ne'
  · apply ind_log_integrable (by fun_prop)
      (fun t ht => q_ne ht.2.1 (ht.1.2.trans hF.a4_le_a2)) (by fun_prop)
    intro t ht
    have : 0 < sp - 1 - t := by linarith [ht.1.2, hF.a4_le_a2]
    exact (div_pos (mul_pos this (hF.X2_of_a4 t ht.1.2)) (by linarith [hF.sp3])).ne'

theorem L2_integrable {s sp k1 k2 k3 : ℝ} (hp : Admissible4 ⟨s, sp, k1, k2, k3⟩) :
    IntervalIntegrable (L2 ⟨s, sp, k1, k2, k3⟩) volume 1 3 := by
  have hF := adm4_facts hp
  have hk21 : 0 < k2 - 1 := by linarith [hF.s2, hF.sk3, hF.k32]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := alpha_vals s sp k1 k2 k3
  unfold L2
  simp only [e0, e1, e3, e8]
  refine IntervalIntegrable.add (IntervalIntegrable.add ?_ ?_) ?_
  · apply ind_log_integrable (by fun_prop)
      (fun t ht => (show (0 : ℝ) < t by linarith [ht.2.1]).ne')
    · exact ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun t ht => (mul_pos hk21 (by linarith [ht.1.2])).ne')
    · intro t ht
      exact (div_pos (by linarith [ht.2.1]) (mul_pos hk21 (by linarith [ht.1.2]))).ne'
  · apply ind_log_integrable (by fun_prop)
      (fun t ht => (show (0 : ℝ) < t by linarith [ht.2.1]).ne') (by fun_prop)
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) hk21).ne'
  · apply ind_log_integrable (by fun_prop)
      (fun t ht => (show (0 : ℝ) < t by linarith [ht.2.1]).ne') (by fun_prop)
    intro t ht
    exact (show (0 : ℝ) < sp - 1 - t by linarith [ht.1.2, hF.a4_le_a2]).ne'

/-- Display 6.3 at `a = 1 − 1/x`, `b = 1 − 1/s'`, `c = s'` for `2 ≤ x < s'`, as used three
times, at `x = s, κ₂, κ₃`, on page 29 for display 6.5. -/
theorem eq3_at {H h : ℝ → ℝ}
    (h63 : ∀ a b c : ℝ, 0 < a → a < b → b < 1 → 2 ≤ a * c → a * c < b * c → b * c ≤ 4 →
        log ((b - a * b) / (a - a * b)) *
            (∫ t in (1 : ℝ)..3, H t * ((sigma0 t + ind (b * c - 1) 3 t) / t)) +
          (∫ t in (1 : ℝ)..3, H t * (ind (a * c - 1) (b * c - 1) t / t *
            log ((1 - a) * (t + 1) / (a * (c - 1 - t))))) ≤
          ∫ t in a..b, h (c * t) / (t * (1 - t)))
    {x sp : ℝ} (hx : 2 ≤ x) (hlt : x < sp) (hsp5 : sp ≤ 5) (hss : 2 ≤ sp - sp / x) :
    log ((sp - 1) / (x - 1)) * (∫ t in (1 : ℝ)..3, H t * kernel63a sp t) +
        (∫ t in (1 : ℝ)..3, H t * kernel63b x sp t) ≤
      ∫ t in (1 - 1 / x)..(1 - 1 / sp), h (sp * t) / (t * (1 - t)) := by
  have hx0 : 0 < x := by linarith
  have hsp0 : 0 < sp := by linarith
  have ha : 0 < 1 - 1 / x := by
    have : 1 / x ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hx
    linarith
  have hab : 1 - 1 / x < 1 - 1 / sp := by
    have : 1 / sp < 1 / x := one_div_lt_one_div_of_lt hx0 hlt
    linarith
  have hb : 1 - 1 / sp < 1 := by
    have : 0 < 1 / sp := by positivity
    linarith
  have eac : (1 - 1 / x) * sp = sp - sp / x := by field_simp
  have ebc : (1 - 1 / sp) * sp = sp - 1 := by field_simp
  have hh := h63 (1 - 1 / x) (1 - 1 / sp) sp ha hab hb
    (by rw [eac]; exact hss) (mul_lt_mul_of_pos_right hab hsp0) (by rw [ebc]; linarith)
  have eL : ((1 - 1 / sp) - (1 - 1 / x) * (1 - 1 / sp)) /
      ((1 - 1 / x) - (1 - 1 / x) * (1 - 1 / sp)) = (sp - 1) / (x - 1) := by
    have : x - 1 ≠ 0 := by linarith
    have : sp - 1 ≠ 0 := by linarith
    field_simp
    ring
  have eG : ∀ t : ℝ, (1 - (1 - 1 / x)) * (t + 1) / ((1 - 1 / x) * (sp - 1 - t)) =
      (t + 1) / ((x - 1) * (sp - 1 - t)) := by
    intro t
    by_cases h0 : sp - 1 - t = 0
    · simp [h0]
    · have : x - 1 ≠ 0 := by linarith
      field_simp
      ring
  rw [eL, eac, ebc, show sp - 1 - 1 = sp - 2 by ring] at hh
  simp only [eG] at hh
  exact hh

/-- **Leaf `proposition4` from its split.** Wu 2004 Proposition 4, page 15, display 3.22, by
the proof on pages 29 and 30: Lemma 5.2, display 6.5, which is derived here from 6.2 and 6.3
of Lemma 6.1 as Wu says, and displays 6.6 to 6.8. Same statement as
`Burst4Split.proposition4`. CONDITIONAL ON `lemma52`, and on Propositions 1 and 2 through
`lemma61_eq2`, `lemma61_eq3` and `corollary1`; displays 6.6 to 6.8, `eq66`, `eq67`, `eq68`, are
PROVED. -/
theorem proposition4 {F f ω : ℝ → ℝ} (hF : IsLinearSieve F f) (hω : IsBuchstab ω) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ H h : ℝ → ℝ,
      RepresentsCorrections F f δ H h → Proposition4 H ω := by
  obtain ⟨d1, hd1, h52⟩ := lemma52 hF hω
  obtain ⟨d2, hd2, h62⟩ := lemma61_eq2 hF
  obtain ⟨d3, hd3, h63⟩ := lemma61_eq3 hF
  obtain ⟨d4, hd4, hA⟩ := corollary1 hF
  refine ⟨min (min d1 d2) (min d3 d4), lt_min (lt_min hd1 hd2) (lt_min hd3 hd4),
    fun δ hδ hδ' H h hR p hp => ?_⟩
  have e1 : δ < d1 := hδ'.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : δ < d2 := hδ'.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : δ < d3 := hδ'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : δ < d4 := hδ'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hdec : AntitoneOn H (Icc (1 : ℝ) 3) :=
    (hA δ hδ e4 H h hR).mono (Icc_subset_Icc le_rfl (by norm_num))
  obtain ⟨s, sp, k1, k2, k3⟩ := p
  have hFa := adm4_facts hp
  have hA3 : Admissible3 s sp := hp.1
  have q52 := h52 δ hδ e1 H h hR ⟨s, sp, k1, k2, k3⟩ hA3 hFa.sk3 hFa.k32 hFa.k21 hFa.k1sp
  have q62s : (∫ t in (1 : ℝ)..3, H t * kernel62 sp t) ≤ H sp :=
    h62 δ hδ e2 H h hR sp hFa.sp3 hFa.sp5
  have q62k : (∫ t in (1 : ℝ)..3, H t * kernel62 k1 t) ≤ H k1 :=
    h62 δ hδ e2 H h hR k1 hFa.k1_3 (hFa.k1sp.trans hFa.sp5)
  have h63' := h63 δ hδ e3 H h hR
  have hk2sp : k2 < sp := hFa.k21.trans_le hFa.k1sp
  have hk3sp : k3 < sp := hFa.k32.trans hk2sp
  have hssp : s < sp := hFa.sk3.trans_lt hk3sp
  have hsp0 : 0 < sp := by linarith [hFa.sp3]
  have hmono : ∀ x y : ℝ, 0 < x → x ≤ y → sp - sp / x ≤ sp - sp / y := fun x y hx hxy => by
    have : sp / y ≤ sp / x := div_le_div_of_nonneg_left hsp0.le hx hxy
    linarith
  have q3s := eq3_at h63' hFa.s2 hssp hFa.sp5 hFa.ssp
  have q32 := eq3_at h63' (by linarith [hFa.s2, hFa.sk3, hFa.k32]) hk2sp hFa.sp5
    ((hFa.ssp).trans (hmono s k2 (by linarith [hFa.s2]) (by linarith [hFa.sk3, hFa.k32])))
  have q33 := eq3_at h63' (by linarith [hFa.s2, hFa.sk3]) hk3sp hFa.sp5
    ((hFa.ssp).trans (hmono s k3 (by linarith [hFa.s2]) hFa.sk3))
  rw [eq66 hdec hp, eq67 hdec hp, eq68 hdec hp] at q52
  -- integrability of the eleven products
  have hk3 : 2 ≤ k3 := by linarith [hFa.s2, hFa.sk3]
  have hk2 : 2 ≤ k2 := by linarith [hFa.s2, hFa.sk3, hFa.k32]
  let K : Fin 11 → ℝ → ℝ := ![kernel62 sp, kernel62 k1, kernel63a sp, kernel63b s sp,
    kernel63a sp, kernel63b k2 sp, kernel63a sp, kernel63b k3 sp,
    L66 ⟨s, sp, k1, k2, k3⟩, L1 ⟨s, sp, k1, k2, k3⟩, L2 ⟨s, sp, k1, k2, k3⟩]
  let c : Fin 11 → ℝ := ![4, 1, log ((sp - 1) / (s - 1)), 1, log ((sp - 1) / (k2 - 1)), 1,
    log ((sp - 1) / (k3 - 1)), 1, 1, 1, 1]
  have hK : ∀ i : Fin 11, IntervalIntegrable (K i) volume 1 3 := by
    intro i
    fin_cases i
    · exact kernel62_integrable hFa.sp3
    · exact kernel62_integrable hFa.k1_3
    · exact kernel63a_integrable (sp - 2)
    · exact kernel63b_integrable hFa.s2
    · exact kernel63a_integrable (sp - 2)
    · exact kernel63b_integrable hk2
    · exact kernel63a_integrable (sp - 2)
    · exact kernel63b_integrable hk3
    · exact L66_integrable hp
    · exact L1_integrable hp
    · exact L2_integrable hp
  have hHK : ∀ i ∈ (Finset.univ : Finset (Fin 11)),
      IntervalIntegrable (fun t => c i * (H t * K i t)) volume 1 3 :=
    fun i _ => (Burst4Split.product_integrable hdec (hK i)).const_mul (c i)
  -- the integral identity of page 30
  have hnull : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∉ ({sp - 2, sp - sp / k2 - 1, sp - sp / k1 - sp / k2} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.toFinite _).measure_zero _)
  have key : (∫ t in (1 : ℝ)..3, H t * Xi2 ⟨s, sp, k1, k2, k3⟩ t) =
      1 / 5 * ∑ i, c i * ∫ t in (1 : ℝ)..3, H t * K i t := by
    have hc : (∫ t in (1 : ℝ)..3, H t * Xi2 ⟨s, sp, k1, k2, k3⟩ t) =
        ∫ t in (1 : ℝ)..3, 1 / 5 * ∑ i, c i * (H t * K i t) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hnull] with t ht hI
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
      rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hI
      rw [Xi2_split hp hI.1.le ht.1 ht.2.1 ht.2.2]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, K, c, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      ring
    rw [hc, intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hHK]
    simp only [intervalIntegral.integral_const_mul]
  show Psi2 ω ⟨s, sp, k1, k2, k3⟩ + (∫ t in (1 : ℝ)..3, H t * Xi2 ⟨s, sp, k1, k2, k3⟩ t) ≤ H s
  rw [key]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, K, c, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  dsimp only at q52
  linarith

/-! ### Part F. The real representatives of Section 3, pages 9 and 10 -/

/-- The empty prime tuple at an even `N ≥ 3`: it lies in `U_k(N)`, its `Φ` is nonnegative and
its `Θ` is positive. This is the witness that makes `H_{k,N₀}(s)` and `h_{k,N₀}(s)` finite. -/
theorem empty_witness {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (k N : ℕ) (hN : 3 ≤ N) (s : ℝ) :
    Wu04.UkData δ k N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) ∧
    0 ≤ Wu04.Phi δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) s ∧
    0 < Wu04.Theta δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hp : 0 < (Real.log N)⁻¹ ^ 4 := by positivity
  refine ⟨Wu04.empty_UkData δ k N (by linarith) (by linarith), ?_, ?_⟩
  · unfold Wu04.Phi
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  · unfold Wu04.Theta
    have hli : 0 < Wu04.li (N : ℝ) := Wu04.li_positive (by linarith)
    have hne : (Wu41.Tset N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4)).Nonempty :=
      ⟨Fin.elim0, Fintype.mem_piFinset.2 fun j => j.elim0⟩
    refine mul_pos (mul_pos (by norm_num) hli) (Finset.sum_pos (fun t _ => ?_) hne)
    have hm : Wu04.modulus t = 1 := by simp [Wu04.modulus]
    have hQ : 0 < Real.log (Wu04.Q δ N) := by
      unfold Wu04.Q
      rw [Real.log_rpow (by linarith)]
      exact mul_pos (by linarith) hl
    rw [hm]
    simp only [Nat.cast_one, one_mul, div_one, Nat.totient_one]
    exact div_pos (CN_pos N) hQ

/-- An even number at least `max N₀ 3`. -/
theorem exists_even_ge (N₀ : ℕ) : ∃ N, Even N ∧ N₀ ≤ N ∧ 3 ≤ N :=
  ⟨2 * (N₀ + 2), even_two_mul _, by omega, by omega⟩

/-- **Leaf `corrections_real` from Proposition 1.** Wu 2004 Section 3, pages 9 and 10: for
`0 < δ < 1/2` below the Proposition 1 thresholds, `0 ≤ H(s) ≤ A(s)` and
`0 ≤ h(s) ≤ A(s) − a(s) + 1` on `[1, 10]`, so both are finite and have real representatives.
The upper bounds use the empty tuple witness `empty_witness`, the second one also the
estimate `Φ ≤ {A(s) + ε} Θ` of the proof of Proposition 1. Same statement as
`Burst4Split.corrections_real`. CONDITIONAL ON `prop1_upper_eps` and `prop1_lower_eps`. -/
theorem corrections_real {F f : ℝ → ℝ} (hF : IsLinearSieve F f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ H h : ℝ → ℝ, RepresentsCorrections F f δ H h := by
  obtain ⟨d1, hd1, hHn⟩ := Hk_nonneg hF
  obtain ⟨d2, hd2, hhn⟩ := hk_nonneg hF
  obtain ⟨d3, hd3, hU⟩ := prop1_upper_eps hF
  refine ⟨min (min d1 d2) (min d3 (1 / 2)), lt_min (lt_min hd1 hd2) (lt_min hd3 (by norm_num)),
    fun δ hδ hδ' => ?_⟩
  have e1 : δ < d1 := hδ'.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : δ < d2 := hδ'.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : δ < d3 := hδ'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : δ < 1 / 2 := hδ'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨fun s => (Wu04.H F δ s).toReal, fun s => (Wu04.h f δ s).toReal, fun s hs => ?_⟩
  -- upper bound for `H`
  have hHup : Wu04.H F δ s ≤ (Wu04.normalized F s : EReal) := by
    refine (iInf_le _ 0).trans (iSup_le fun N₀ => sSup_le ?_)
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨N, hEv, hN0, hN3⟩ := exists_even_ge N₀
    obtain ⟨hUk, hPhi, hTh⟩ := empty_witness hδ e4 (0 + 1) N hN3 s
    have := hc N hN0 (by omega) hEv 0 Fin.elim0 _ hUk
    have : c ≤ Wu04.normalized F s := by
      by_contra hcon
      have : (Wu04.normalized F s - c) * Wu04.Theta δ N 0 Fin.elim0
          (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) < 0 := mul_neg_of_neg_of_pos (by linarith) hTh
      linarith
    show ((c : ℝ) : EReal) ≤ _
    exact_mod_cast this
  have hH0 : (0 : EReal) ≤ Wu04.H F δ s := le_iInf fun k => hHn δ hδ e1 (k + 1) (by omega) s hs
  -- upper bound for `h`
  obtain ⟨N₁, hN₁⟩ := hU δ hδ e3 1 le_rfl s hs 1 one_pos
  have hhup : Wu04.h f δ s ≤ ((Wu04.normalized F s + 1 - Wu04.normalized f s : ℝ) : EReal) := by
    refine (iInf_le _ 0).trans (iSup_le fun N₀ => sSup_le ?_)
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨N, hEv, hN0, hN3⟩ := exists_even_ge (max N₀ N₁)
    obtain ⟨hUk, hPhi, hTh⟩ := empty_witness hδ e4 (0 + 1) N hN3 s
    have hlo := hc N (le_of_max_le_left hN0) (by omega) hEv 0 Fin.elim0 _ hUk
    have hhi := hN₁ N (le_of_max_le_right hN0) (by omega) hEv 0 Fin.elim0 _ hUk
    have : c ≤ Wu04.normalized F s + 1 - Wu04.normalized f s := by
      by_contra hcon
      have : (Wu04.normalized F s - -1) * Wu04.Theta δ N 0 Fin.elim0
            (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) <
          (Wu04.normalized f s + c) * Wu04.Theta δ N 0 Fin.elim0
            (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) :=
        mul_lt_mul_of_pos_right (by linarith) hTh
      linarith
    show ((c : ℝ) : EReal) ≤ _
    exact_mod_cast this
  have hh0 : (0 : EReal) ≤ Wu04.h f δ s := le_iInf fun k => hhn δ hδ e2 (k + 1) (by omega) s hs
  refine ⟨EReal.coe_toReal ?_ ?_, EReal.coe_toReal ?_ ?_⟩
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hHup
  · exact ne_bot_of_le_ne_bot (by simp) hH0
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hhup
  · exact ne_bot_of_le_ne_bot (by simp) hh0

/-! ### Part H. The last display of page 31 -/

theorem Tset_zero (N : ℕ) (V : Fin 0 → ℝ) (Δ : ℝ) : Wu41.Tset N 0 V Δ = {Fin.elim0} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  exact ⟨Fintype.mem_piFinset.2 fun j => j.elim0, fun x _ => funext fun j => j.elim0⟩

theorem modulus_zero (t : Fin 0 → ℕ) : Wu04.modulus t = 1 := by simp [Wu04.modulus]

/-- `Φ(N, {1}, s) = S(A; P(N), Q^{1/s})`, the case `σ = {1}` of the definition on page 9. -/
theorem Phi_empty (δ s : ℝ) (N : ℕ) (Δ : ℝ) :
    Wu04.Phi δ N 0 Fin.elim0 Δ s = Wu41.S (Wu04.A N) 1 N (Wu04.Q δ N ^ (1 / s)) := by
  unfold Wu04.Phi
  rw [Tset_zero, Finset.sum_singleton, modulus_zero]
  simp only [Nat.cast_one, one_mul, div_one]

/-- `Θ(N, {1}) = 4 li(N) C_N / log Q`, the case `σ = {1}` of the definition on page 10. -/
theorem Theta_empty (δ : ℝ) (N : ℕ) (Δ : ℝ) :
    Wu04.Theta δ N 0 Fin.elim0 Δ = 4 * Wu04.li N * (CN N / Real.log (Wu04.Q δ N)) := by
  unfold Wu04.Theta
  rw [Tset_zero, Finset.sum_singleton, modulus_zero]
  simp only [Nat.cast_one, one_mul, div_one, Nat.totient_one]

/-- Page 31: `D(N) ≤ S(A; P(N), z) + z + 1`. A Goldbach prime `N − p ≥ z` survives the sieve;
the primes `N − p < z` number at most `z + 1`. -/
theorem D_le_S (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (D N : ℝ) ≤ (Wu41.S (Wu04.A N) 1 N z : ℝ) + z + 1 := by
  classical
  have key : D N ≤ Wu41.S (Wu04.A N) 1 N z + ⌈z⌉₊ := by
    have hS : Wu41.S (Wu04.A N) 1 N z =
        (Finset.filter (fun a => 1 ∣ a ∧ Wu41.Sifted N z a) (Wu04.A N)).card := by
      unfold Wu41.S; congr
    rw [hS]
    unfold D
    refine (Finset.card_le_card_of_injOn (fun p => N - p)
      (t := Finset.filter (fun a => 1 ∣ a ∧ Wu41.Sifted N z a) (Wu04.A N) ∪
        Finset.range ⌈z⌉₊) ?_ ?_).trans ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hp
      obtain ⟨hpN, hpp, hΩ⟩ := hp
      have hprime : (N - p).Prime := ArithmeticFunction.cardFactors_eq_one_iff_prime.1 hΩ
      simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_range, Set.mem_union,
        Set.mem_setOf_eq, Set.mem_Iio]
      rcases lt_or_ge ((N - p : ℕ) : ℝ) z with h | h
      · exact Or.inr (Nat.lt_ceil.2 h)
      · left
        refine ⟨Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_range.2 hpN, hpp⟩, rfl⟩,
          one_dvd _, fun q hq hqz _ hqa => ?_⟩
        have := (Nat.prime_dvd_prime_iff_eq hq hprime).1 hqa
        rw [this] at hqz
        linarith
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hp hq
      simp only at hpq
      omega
    · exact (Finset.card_union_le _ _).trans (by rw [Finset.card_range])
  have h1 : (D N : ℝ) ≤ (Wu41.S (Wu04.A N) 1 N z : ℝ) + (⌈z⌉₊ : ℝ) := by exact_mod_cast key
  have h2 : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one hz
  linarith

/-- Display 3.3 of Lemma 3.2, page 9, at `k = 1`, `σ = {1}`, `s = 2.2`, page 31: every
`c < H(2.2)` satisfies `c < 1` and `Φ(N, {1}, 2.2) ≤ (A(2.2) − c) Θ(N, {1})` with
`A(2.2) = 1`, for all large even `N`. PROVED from the definitions of page 10. -/
theorem display33_empty {F f : ℝ → ℝ} (hF : IsLinearSieve F f) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < 1 / 2) {H h : ℝ → ℝ} (hR : RepresentsCorrections F f δ H h) {c : ℝ}
    (hc : c < H 2.2) :
    c < 1 ∧ ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N → 3 ≤ N →
      Wu04.Phi δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) 2.2 ≤
        (1 - c) * Wu04.Theta δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) := by
  have hE : ((c : ℝ) : EReal) < Wu04.H F δ 2.2 := by
    rw [← (hR 2.2 ⟨by norm_num, by norm_num⟩).1]
    exact_mod_cast hc
  have h1 : Wu04.H F δ 2.2 ≤ Wu04.Hk F δ 1 2.2 := iInf_le (fun k => Wu04.Hk F δ (k + 1) 2.2) 0
  obtain ⟨N₀, hN₀⟩ := lt_iSup_iff.1 (hE.trans_le h1)
  obtain ⟨_, ⟨c', hc', rfl⟩, hlt⟩ := lt_sSup_iff.1 hN₀
  have hcc : c < c' := by exact_mod_cast (show ((c : ℝ) : EReal) < ((c' : ℝ) : EReal) from hlt)
  have hA : Wu04.normalized F 2.2 = 1 := normalized_eq_one hF (by norm_num) (by norm_num)
  have hc'1 : c' ≤ 1 := by
    obtain ⟨N, hEv, hN0, hN3⟩ := exists_even_ge N₀
    obtain ⟨hUk, hPhi, hTh⟩ := empty_witness hδ0 hδ 1 N hN3 2.2
    have := hc' N hN0 (by omega) hEv 0 Fin.elim0 _ hUk
    rw [hA] at this
    by_contra hcon
    have : (1 - c') * Wu04.Theta δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hTh
    linarith
  refine ⟨by linarith, N₀, fun N hEv hN0 hN3 => ?_⟩
  obtain ⟨hUk, hPhi, hTh⟩ := empty_witness hδ0 hδ 1 N hN3 2.2
  have := hc' N hN0 (by omega) hEv 0 Fin.elim0 _ hUk
  rw [hA] at this
  exact this.trans (mul_le_mul_of_nonneg_right (by linarith) hTh.le)

/-- `li(x) ≤ (1 + ε) x / log x` for large `x`, the form of `li(N) ∼ N / log N` used on page 31.
PROVED by splitting `∫₂ˣ dt/log t` at `x^r`. -/
theorem li_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, Wu04.li x ≤ (1 + ε) * (x / Real.log x) := by
  set r : ℝ := (2 + ε) / (2 + 2 * ε) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; linarith
  have hrinv : 1 / r ≤ 1 + ε / 2 := by
    rw [hr, one_div_div, div_le_iff₀ (by positivity)]; nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `log x ≤ (ε/2) log 2 · x^{1−r}` eventually
  have hlo := (isLittleO_log_rpow_atTop (show 0 < 1 - r by linarith)).bound
    (show 0 < ε / 2 * Real.log 2 by positivity)
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 hlo
  refine ⟨max x₁ (max 3 ((2 : ℝ) ^ (1 / r))), fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2r : (2 : ℝ) ^ (1 / r) ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set y := x ^ r with hy
  have hy2 : 2 ≤ y := by
    have := Real.rpow_le_rpow (by positivity) hx2r hr0.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hr0.ne', Real.rpow_one] at this
  have hyx : y ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) hr1.le
    rwa [Real.rpow_one] at this
  have hly : Real.log y = r * Real.log x := Real.log_rpow hx0 r
  have hlyp : 0 < Real.log y := by rw [hly]; positivity
  have hcont : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      IntervalIntegrable (fun t => (Real.log t)⁻¹) MeasureTheory.volume a b := by
    intro a b ha hab
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (ContinuousOn.log continuousOn_id fun t ht => ?_) fun t ht => ?_
    · rw [uIcc_of_le hab] at ht; show t ≠ 0; exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
    · rw [uIcc_of_le hab] at ht; show Real.log t ≠ 0; exact (Real.log_pos (by linarith [ht.1])).ne'
  have hsplit : Wu04.li x = (∫ t in (2 : ℝ)..y, (Real.log t)⁻¹) +
      ∫ t in y..x, (Real.log t)⁻¹ := by
    unfold Wu04.li
    rw [intervalIntegral.integral_add_adjacent_intervals (hcont 2 y le_rfl hy2)
      (hcont y x hy2 hyx)]
  have hA : (∫ t in (2 : ℝ)..y, (Real.log t)⁻¹) ≤ y / Real.log 2 := by
    have := intervalIntegral.integral_mono_on hy2 (hcont 2 y le_rfl hy2)
      (intervalIntegrable_const (c := (Real.log 2)⁻¹)) (fun t ht =>
        inv_anti₀ hl2 (Real.log_le_log (by norm_num) ht.1))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have : (y - 2) * (Real.log 2)⁻¹ ≤ y / Real.log 2 := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hB : (∫ t in y..x, (Real.log t)⁻¹) ≤ x / (r * Real.log x) := by
    have := intervalIntegral.integral_mono_on hyx (hcont y x hy2 hyx)
      (intervalIntegrable_const (c := (Real.log y)⁻¹)) (fun t ht =>
        inv_anti₀ hlyp (Real.log_le_log (by linarith) ht.1))
    rw [intervalIntegral.integral_const, smul_eq_mul, hly] at this
    have : (x - y) * (r * Real.log x)⁻¹ ≤ x / (r * Real.log x) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    rw [hly] at hlyp
    linarith
  have hC : y / Real.log 2 ≤ ε / 2 * (x / Real.log x) := by
    have h := hx₁ x hx1
    rw [Real.norm_of_nonneg hlx.le, Real.norm_of_nonneg (by positivity)] at h
    -- `y · x^{1−r} = x`
    have hyx' : y * x ^ (1 - r) = x := by
      rw [hy, ← Real.rpow_add hx0, show r + (1 - r) = 1 by ring, Real.rpow_one]
    rw [div_le_iff₀ hl2]
    have : ε / 2 * (x / Real.log x) * Real.log 2 = ε / 2 * Real.log 2 * x / Real.log x := by
      ring
    rw [this, le_div_iff₀ hlx]
    calc y * Real.log x ≤ y * (ε / 2 * Real.log 2 * x ^ (1 - r)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ε / 2 * Real.log 2 * (y * x ^ (1 - r)) := by ring
      _ = ε / 2 * Real.log 2 * x := by rw [hyx']
  have hD : x / (r * Real.log x) ≤ (1 + ε / 2) * (x / Real.log x) := by
    rw [show x / (r * Real.log x) = 1 / r * (x / Real.log x) by field_simp]
    exact mul_le_mul_of_nonneg_right hrinv (by positivity)
  rw [hsplit]
  nlinarith

/-- `N^{1/4} + 1 ≤ κ N / log² N` for large `N`. -/
theorem small_term {κ : ℝ} (hκ : 0 < κ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, x ^ (1 / 4 : ℝ) + 1 ≤ κ * (x / Real.log x ^ 2) := by
  have hlo := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).bound one_pos
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 hlo
  refine ⟨max x₁ (max 3 ((2 / κ) ^ 2)), fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxk : (2 / κ) ^ 2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have h := hx₁ x hx1
  rw [Real.norm_of_nonneg hlx.le, Real.norm_of_nonneg (by positivity), one_mul] at h
  have e8 : (x ^ (1 / 8 : ℝ)) ^ 2 = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have e4 : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have e2 : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hq1 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog2 : Real.log x ^ 2 ≤ x ^ (1 / 4 : ℝ) := by
    rw [← e8]; exact pow_le_pow_left₀ hlx.le h 2
  have hs : 2 / κ ≤ x ^ (1 / 2 : ℝ) := by
    have := Real.sqrt_le_sqrt hxk
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow] at this
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have h2 : 2 ≤ κ * x ^ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hκ] at hs; linarith
  calc (x ^ (1 / 4 : ℝ) + 1) * Real.log x ^ 2 ≤ (2 * x ^ (1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ) :=
        mul_le_mul (by linarith) hlog2 (by positivity) (by positivity)
    _ = 2 * x ^ (1 / 2 : ℝ) := by rw [mul_assoc, e4]
    _ ≤ κ * x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = κ * x := by rw [mul_assoc, e2]

/-- **Leaf `theorem1_final_display` PROVED.** Wu 2004 page 31, last display: Lemma 3.2 with
`σ = {1}` and `s = 2.2`, `D(N) ≤ S(A; P(N), N^{(1/2−δ)/2.2}) = Φ(N, {1}, 2.2) ≤
{A(2.2) − H_{1,N₀}(2.2)} 4 C_N li(N)/log N^{1/2−δ}`, with `A(2.2) = 1` and `li(N) ∼ N/log N`.
Same statement as `Burst4Split.theorem1_final_display`. -/
theorem theorem1_final_display {F f : ℝ → ℝ} (hF : IsLinearSieve F f)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {H h : ℝ → ℝ}
    (hR : RepresentsCorrections F f δ H h) {c : ℝ} (hc : c < H 2.2) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N →
      (D N : ℝ) ≤ (1 + ε) * (8 * (1 - c) / (1 - 2 * δ)) * Θ N := by
  obtain ⟨hc1, N₀, hN₀⟩ := display33_empty hF hδ0 (by linarith) hR hc
  set K := 8 * (1 - c) / (1 - 2 * δ) with hK
  have hK0 : 0 < K := div_pos (by linarith) (by linarith)
  have htw := LeanLab.ChenExplicit.twinC_pos
  obtain ⟨x₀, hx₀⟩ := li_upper (show 0 < ε / 2 by linarith)
  obtain ⟨x₁, hx₁⟩ := small_term (show 0 < ε / 2 * K * LeanLab.ChenExplicit.twinC by positivity)
  refine ⟨max N₀ (max 3 (max ⌈x₀⌉₊ ⌈x₁⌉₊)), fun N hEv hN => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN3 : 3 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNx0 : x₀ ≤ N := (Nat.le_ceil x₀).trans (by exact_mod_cast
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN)
  have hNx1 : x₁ ≤ N := (Nat.le_ceil x₁).trans (by exact_mod_cast
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN)
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0r : (0 : ℝ) < N := by linarith
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  set Δ := 1 + 3 / 2 * (Real.log N)⁻¹ ^ 4
  set z := Wu04.Q δ N ^ (1 / (2.2 : ℝ)) with hz
  have hQ : Wu04.Q δ N = (N : ℝ) ^ (1 / 2 - δ) := rfl
  have hz0 : 0 ≤ z := Real.rpow_nonneg (Real.rpow_nonneg hN0r.le _) _
  have hz4 : z ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [hz, hQ, ← Real.rpow_mul hN0r.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hlogQ : Real.log (Wu04.Q δ N) = (1 / 2 - δ) * Real.log N := by
    rw [hQ, Real.log_rpow hN0r]
  -- the chain of page 31
  have h1 := D_le_S N hz0
  rw [← Phi_empty δ 2.2 N Δ] at h1
  have h2 := hN₀ N hEv hN0 hN3
  rw [Theta_empty, hlogQ] at h2
  have hli := hx₀ N hNx0
  have hsm := hx₁ N hNx1
  have hCN : LeanLab.ChenExplicit.twinC ≤ CN N := by
    unfold CN; have := oddFactor_one_le N; nlinarith
  have hCN0 : 0 < CN N := CN_pos N
  have hΘ : Θ N = CN N * N / Real.log N ^ 2 := rfl
  -- the main term
  have hmain : (1 - c) * (4 * Wu04.li N * (CN N / ((1 / 2 - δ) * Real.log N))) ≤
      (1 + ε / 2) * K * Θ N := by
    have e : (1 - c) * (4 * Wu04.li N * (CN N / ((1 / 2 - δ) * Real.log N))) =
        K * CN N / Real.log N * Wu04.li N := by
      rw [hK]; field_simp; ring
    rw [e, hΘ]
    have hk : 0 ≤ K * CN N / Real.log N := by positivity
    calc K * CN N / Real.log N * Wu04.li N ≤
          K * CN N / Real.log N * ((1 + ε / 2) * (N / Real.log N)) :=
          mul_le_mul_of_nonneg_left hli hk
      _ = (1 + ε / 2) * K * (CN N * N / Real.log N ^ 2) := by field_simp
  -- the small term
  have hsmall : z + 1 ≤ ε / 2 * K * Θ N := by
    have : ε / 2 * K * LeanLab.ChenExplicit.twinC * (N / Real.log N ^ 2) ≤ ε / 2 * K * Θ N := by
      rw [hΘ, show ε / 2 * K * LeanLab.ChenExplicit.twinC * (N / Real.log N ^ 2) =
        ε / 2 * K * (LeanLab.ChenExplicit.twinC * N / Real.log N ^ 2) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCN hN0r.le) (by positivity)
    linarith
  have hfin : (1 + ε) * (8 * (1 - c) / (1 - 2 * δ)) * Θ N =
      (1 + ε / 2) * K * Θ N + ε / 2 * K * Θ N := by rw [hK]; ring
  rw [hfin]
  linarith

/-! ### Part G. The new top level -/

/-- **Wu 2004 Theorem 1 from the pass 2 split.** The exact statement of `wu2004_thm1`,
`GoldbachUpper 7.8209`, proved as `Burst4Split.wu2004_thm1_of_split` but with the leaves
`corrections_real`, `proposition1`, `corollary1`, `proposition3`, `proposition4` replaced by
their splits in this file, and `table_kernel_integrable` and `theorem1_final_display` PROVED.
CONDITIONAL ON the remaining eight sorry leaves: `prop1_upper_eps`, `prop1_lower_eps`,
`proposition2_H`, `proposition2_h`, `lemma51`, `lemma52`, `Burst4Split.table1_Psi2` and
`Burst4Split.integral_matrix_bound`. -/
theorem wu2004_thm1_of_p2 : GoldbachUpper 7.8209 := by
  obtain ⟨F, f, ω, hF, hω⟩ := Task275.standard_functions
  obtain ⟨d1, hd1, hC⟩ := corrections_real hF
  obtain ⟨d2, hd2, h1⟩ := proposition1 hF
  obtain ⟨d3, hd3, hA⟩ := corollary1 hF
  obtain ⟨d4, hd4, h3⟩ := proposition3 hF hω
  obtain ⟨d5, hd5, h4⟩ := proposition4 hF hω
  set m := min d1 (min d2 (min d3 (min d4 d5))) with hm
  have hm0 : 0 < m := by
    simp only [hm, lt_min_iff]
    exact ⟨hd1, hd2, hd3, hd4, hd5⟩
  set δ := min (m / 2) (1 / 10000000) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδm : δ < m := (min_le_left _ _).trans_lt (by linarith)
  have hδs : δ ≤ 1 / 10000000 := min_le_right _ _
  have hm1 : m ≤ d1 := min_le_left _ _
  have hm2 : m ≤ d2 := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : m ≤ d3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm4 : m ≤ d4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hm5 : m ≤ d5 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨H, h, hR⟩ := hC δ hδ0 (hδm.trans_le hm1)
  have hnn := h1 δ hδ0 (hδm.trans_le hm2) H h hR
  have hanti := hA δ hδ0 (hδm.trans_le hm3) H h hR
  have hp3 := h3 δ hδ0 (hδm.trans_le hm4) H h hR
  have hp4 := h4 δ hδ0 (hδm.trans_le hm5) H h hR
  have hdec : AntitoneOn H (Icc (1 : ℝ) 3) :=
    hanti.mono (Icc_subset_Icc le_rfl (by norm_num))
  have hT : Wu04Discretization.TableInputs H :=
    { nonnegative := fun t ht => (hnn t ⟨ht.1, by linarith [ht.2]⟩).1
      decreasing := hdec
      kernel_nonnegative := fun i t ht => Wu04Table.tableKernel_nonnegative i ht
      kernel_integrable := table_kernel_integrable
      product_integrable := fun i =>
        Burst4Split.product_integrable hdec (table_kernel_integrable i)
      functional := Wu04Table.functional_rows hω hp3 hp4 (Burst4Split.table1_Psi2 hω) }
  have hx : (223938 / 10000000 : ℝ) ≤ H (2.2 : ℝ) :=
    Wu04Discretization.correction_of_functional H hT Burst4Split.integral_matrix_bound
  have hc : (223937 / 10000000 : ℝ) < H 2.2 := by linarith
  obtain ⟨N₀, hN₀⟩ := theorem1_final_display hF hδ0 (by linarith) hR hc
    (ε := 1 / 1000000) (by norm_num)
  refine ⟨N₀, fun N hE hN => (hN₀ N hE hN).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Burst4Split.final_constant hδ0 hδs) (Θ_nonneg N)

end LeanLab.ChenDoubleSieve.Burst8P2

#print axioms LeanLab.ChenDoubleSieve.Burst8P2.wu2004_thm1_of_p2
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.table_kernel_integrable
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.proposition1
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.eq61
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.eq68
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.eq66
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.eq67
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.eq62
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.eq63
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.eq64
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.lemma61_eq2
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.lemma61_eq3
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.corrections_real
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.theorem1_final_display
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.li_upper
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.D_le_S
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.empty_witness
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.corollary1
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.corollary1_low
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.proposition3
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.proposition4
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.Xi2_split
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.Xi1_split
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.ereal_nonneg_of_forall
