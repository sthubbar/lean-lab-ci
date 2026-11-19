import LeanLab.ChenDoubleSieve.Table1Algebra
import LeanLab.ChenDoubleSieve.Xi2Signs

/-!
Kernel integrability for Wu 2004 equations 3.21 and 3.22 and page 30 equations 7.1 and 7.2.
Source: https://arxiv.org/abs/0705.1652.
The six declarations below are moved byte for byte from Burst8P2.
This dependency module lets Burst4Split reuse their existing proofs without an import cycle.
AI wrote the Lean code. Binary Goldbach is open.
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

/-- The sign conditions of `Wu04Functional.tableXi2_log_signs`, which Wu 2004 obtains for the
four Table 1 rows: on each support interval of display 3.22 the denominator of the logarithm is
positive and at most its numerator. PROVED from `tableXi2_log_signs`, no new definition. -/
theorem tableParams_Xi2Signs (i : Fin 4) :
  ∀ t ∈ Icc (1 : ℝ) 3,
    let a := alpha (tableParams i)
    let P := ((tableParams i).s-1)*((tableParams i).sp-1)*((tableParams i).k1-1)*((tableParams i).k2-1)*((tableParams i).k3-1)
    ((a 1 ≤ t ∧ t ≤ 3) → 0 < P ∧ P ≤ (t+1)^5) ∧
    ((a 8 ≤ t ∧ t ≤ a 0) → 0 < ((tableParams i).k2-1)*((tableParams i).k1-1-t) ∧ ((tableParams i).k2-1)*((tableParams i).k1-1-t) ≤ t+1) ∧
    ((a 4 ≤ t ∧ t ≤ a 1) → 0 < ((tableParams i).k3-1)*((tableParams i).sp-1-t) ∧ ((tableParams i).k3-1)*((tableParams i).sp-1-t) ≤ t+1) ∧
    ((a 2 ≤ t ∧ t ≤ a 1) → 0 < ((tableParams i).s-1)*((tableParams i).sp-1-t) ∧ ((tableParams i).s-1)*((tableParams i).sp-1-t) ≤ t+1) ∧
    ((a 0 ≤ t ∧ t ≤ a 1) → 0 < ((tableParams i).k1-1)*((tableParams i).k2-1) ∧ ((tableParams i).k1-1)*((tableParams i).k2-1) ≤ (t+1)^2) ∧
    ((a 6 ≤ t ∧ t ≤ a 4) →
      0 < ((tableParams i).k1*(tableParams i).sp-(tableParams i).sp-(tableParams i).k1*t)*((tableParams i).k3*(tableParams i).sp-(tableParams i).sp-(tableParams i).k3*t) ∧
      ((tableParams i).k1*(tableParams i).sp-(tableParams i).sp-(tableParams i).k1*t)*((tableParams i).k3*(tableParams i).sp-(tableParams i).sp-(tableParams i).k3*t) ≤ (tableParams i).sp^2) ∧
    ((a 4 ≤ t ∧ t ≤ a 7) → 0 < (tableParams i).k1*(tableParams i).sp-(tableParams i).sp-(tableParams i).k1*t ∧
      (tableParams i).k1*(tableParams i).sp-(tableParams i).sp-(tableParams i).k1*t ≤ (tableParams i).sp*((tableParams i).sp-1-t)) ∧
    ((a 5 ≤ t ∧ t ≤ a 7) → 0 < (tableParams i).k2*(tableParams i).sp-(tableParams i).sp-(tableParams i).k2*t ∧
      (tableParams i).k2*(tableParams i).sp-(tableParams i).sp-(tableParams i).k2*t ≤ (tableParams i).sp) ∧
    ((a 7 ≤ t ∧ t ≤ a 1) → 0 < (1 : ℝ) ∧ 1 ≤ (tableParams i).sp-1-t) :=
  fun _ ht => tableXi2_log_signs i ht

/-- `Ξ₂(·; s, s', κ₁, κ₂, κ₃)` of display 3.22, page 15, is integrable on `[1, 3]` whenever
`3 < s'` and the logarithms have positive arguments on their supports. -/
theorem Xi2_integrable {p : Params} (hsp : 3 < p.sp) (hS :
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
    ((a 7 ≤ t ∧ t ≤ a 1) → 0 < (1 : ℝ) ∧ 1 ≤ p.sp-1-t)) :
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



end LeanLab.ChenDoubleSieve.Burst8P2
